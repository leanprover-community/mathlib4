/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init
public meta import Mathlib.Lean.MessageData.Trace

/-!
# The `#defeq_abuse` tactic and command combinators

`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting, helping to diagnose where Mathlib relies on
definitional equality that isn't available at instance transparency.

`#defeq_abuse in cmd` does the same for commands (e.g. `instance` declarations), where
type class synthesis failures may occur during elaboration rather than during a tactic.
It additionally traces `Meta.synthInstance` to group `isDefEq` failures by the synthesis
application that triggered them.

## Usage

### Tactic mode
```
#defeq_abuse in rw [Set.disjoint_singleton_right]
```

will report something like:
```
Tactic fails with `backward.isDefEq.respectTransparency true` but succeeds with `false`.
The following isDefEq checks are the root causes of the failure:
  (i : ℕ) → (fun a ↦ Prop) i =?= Set ℕ
```

### Command mode
```
#defeq_abuse in
instance {V : Type} [AddCommGroup V] [Module ℝ V] {l : Submodule ℝ V} :
    Module.Free ℝ l := Module.Free.of_divisionRing ℝ l
```

will report the synthesis failures grouped by instance application.
-/

public meta section

open Lean MessageData Meta Elab Tactic Command

namespace Mathlib.Tactic.DefEqAbuse

/-- Extract the instance name from a rendered `apply @Foo to Goal` trace header.
Returns the string between `"apply "` and `" to "`.

Note: this is fragile string matching against Lean's `Meta.synthInstance` trace format.
If the trace format changes, this function will silently return the original string.
Once https://github.com/leanprover/lean4/pull/12699 is available,
these nodes will have trace class `Meta.synthInstance.apply` and can be identified
structurally via `td.cls` instead of string-matching on the header. -/
private def extractInstName (s : String) : String :=
  match s.splitOn "apply " with
  | [_, rest] => match rest.splitOn " to " with
    | name :: _ => name.trimAscii.toString
    | _ => s
  | _ => s

/-- Only applies `f` to `Meta.isDefEq` trace nodes. if `skipRetry` is `true` (the default), skips
`Meta.isDefEq.onFailure` nodes. -/
@[inline] def onlyOnDefEqNodes {m} [Monad m] {α}
    (f : TraceData → MessageData → Array MessageData → m (VisitStep α))
    (skipRetry := true) :
    TraceData → MessageData → Array MessageData → m (VisitStep α) :=
  fun td header children => do
    if skipRetry && td.cls == `Meta.isDefEq.onFailure then return .ascend
    unless (`Meta.isDefEq).isPrefixOf td.cls do return .descend
    f td header children

/-- Find the deepest failing `Meta.isDefEq` trace nodes (leaf failures).
Skips `onFailure` retry nodes and ignores ✅ branches (recovered failures aren't root causes).
Note: status is currently determined by parsing emoji from the rendered header string.
Once https://github.com/leanprover/lean4/pull/12698 is available, use `td.result?` instead. -/
private partial def findLeafFailures (msg : MessageData) : BaseIO (Array MessageData) :=
  msg.visitTraceNodesM <| onlyOnDefEqNodes fun td header children => do
    unless traceResultOf (← header.toString) matches some .failure do
      return .ascend
    let childFailures ← visitWithM children findLeafFailures
    -- Leaf failure: deepest `❌` node with no deeper `❌` children
    return .ascend <| if childFailures.isEmpty then #[header] else childFailures

/-- Collect rendered check strings from `Meta.isDefEq` trace nodes matching a status predicate.
Returns a `HashSet` of emoji-stripped header strings. -/
private partial def collectIsDefEqChecks (pred : TraceResult → Bool)
    (msg : MessageData) : BaseIO (Std.HashSet String) :=
  msg.visitTraceNodesM <| onlyOnDefEqNodes fun td header children => do
    let headerStr ← header.toString
    if let some status := traceResultOf headerStr then
      if pred status then
        return .descend (butFirst := some {stripTraceResultPrefix headerStr})
    return .descend

-- !! Is this expected to only be run on strict traces? If so, let's rename.
/-- Find the deepest `Meta.isDefEq` transition points: nodes that fail in the strict trace
but whose check string appears as a success in the permissive trace and does NOT also appear
as a failure in the permissive trace (which would indicate the check is context-dependent
rather than transparency-dependent).
A "deepest transition point" has no descendant transition points.
Falls back to `findLeafFailures` behavior when `permSuccesses` is empty. -/
private partial def findTransitionFailures (permSuccesses : Std.HashSet String)
    (permFailures : Std.HashSet String)
    (msg : MessageData) : BaseIO (Array MessageData) :=
  if permSuccesses.isEmpty then findLeafFailures msg
  else msg.visitTraceNodesM <| onlyOnDefEqNodes fun td header children => do
    let headerStr ← header.toString
    unless traceResultOf headerStr matches some .failure do return .descend
    let checkStr := stripTraceResultPrefix headerStr
    if permSuccesses.contains checkStr && !permFailures.contains checkStr then
      -- Transition point: fails strict, succeeds permissive, doesn't also fail permissive.
      -- Look for deeper transition points among children.
      let childTransitions ← visitWithM children <|
        findTransitionFailures permSuccesses permFailures
      return .ascend <|
        -- Deepest transition point: no deeper transition-point children.
        if childTransitions.isEmpty then return #[header] else return childTransitions
    else
      -- Not a transition point (fails in both modes, strict-only, or ambiguous).
      -- Still recurse: children may contain transition points.
      return .descend

/-- Within a synthesis trace, find failing `apply @Instance to Goal` nodes
and their `isDefEq` transition failures.
Once https://github.com/leanprover/lean4/pull/12699 is available, the `headerStr.contains "apply"`
check can be replaced with ``td.cls == `Meta.synthInstance.apply``. -/
private partial def findSynthAppFailures (permSuccesses permFailures : Std.HashSet String)
    (msg : MessageData) : BaseIO (Array (MessageData × Array MessageData)) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if traceResultOf headerStr matches some .failure && headerStr.contains "apply " then
        let failures ← visitWithM children <|
          findTransitionFailures permSuccesses permFailures
        if !failures.isEmpty then
          return .ascend #[(header, failures)]
    return .descend

/-- Find top-level synthesis failures and their `isDefEq` root causes.
Only enters failing synthesis nodes to avoid reporting recovered sub-attempts. -/
private partial def findSynthFailures (permSuccesses permFailures : Std.HashSet String)
    (msg : MessageData) : BaseIO (Array (MessageData × Array MessageData)) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if traceResultOf headerStr matches some .failure then
        visitWithAndAscendM children <| findSynthAppFailures permSuccesses permFailures
      else return .ascend
    -- Skip isDefEq/synthInstance subtrees that aren't top-level synthesis
    else if !(`Meta.isDefEq).isPrefixOf td.cls && !(`Meta.synthInstance).isPrefixOf td.cls then
      return .descend
    else return .ascend

/-- Collect instance names from successful `apply @Instance to Goal` trace nodes.
Once https://github.com/leanprover/lean4/pull/12699 is available, the `headerStr.contains "apply"`
check can be replaced with `td.cls == `Meta.synthInstance.apply``. -/
private partial def findSynthSuccessApps (msg : MessageData) : BaseIO (Std.HashSet String) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.contains "apply" && traceResultOf headerStr == some .success then
        return .descend (butFirst := some {extractInstName headerStr})
    return .descend

/-- Analyze strict and permissive trace messages to find isDefEq transition failures
and (optionally) synthesis-grouped failures.
Returns `(flatFailures, synthGroupedFailures)`. -/
private def analyzeTraces (strictMsgs permMsgs : Array MessageData)
    (includeSynth : Bool := false) :
    BaseIO (Array MessageData × Array (MessageData × Array MessageData)) := do
  -- Build sets of permissive successes and failures for transition-point detection.
  let mut permSuccesses : Std.HashSet String := {}
  let mut permFailures : Std.HashSet String := {}
  for msg in permMsgs do
    permSuccesses := permSuccesses.union (← collectIsDefEqChecks (· == .success) msg)
    permFailures := permFailures.union (← collectIsDefEqChecks (· == .failure) msg)
  -- Find flat transition failures in strict traces.
  let mut transitionFailures : Array MessageData := #[]
  for msg in strictMsgs do
    transitionFailures := transitionFailures ++
      (← findTransitionFailures permSuccesses permFailures msg)
  let uniqueFailures ← dedupByString transitionFailures
  -- Optionally find synthesis-grouped failures.
  if !includeSynth then
    return (uniqueFailures, #[])
  let mut permissiveSuccessApps : Std.HashSet String := {}
  for msg in permMsgs do
    permissiveSuccessApps := permissiveSuccessApps.union (← findSynthSuccessApps msg)
  let mut synthResults : Array (MessageData × Array MessageData) := #[]
  for msg in strictMsgs do
    synthResults := synthResults.append
      (← findSynthFailures permSuccesses permFailures msg)
  -- Filter to only applications that succeed with permissive transparency.
  let filteredResults ← synthResults.filterM fun (app, _) => do
    return permissiveSuccessApps.contains (extractInstName (← app.toString))
  -- Dedup failures within each synth result.
  let dedupedResults ← filteredResults.mapM fun (app, failures) => do
    return (app, ← dedupByString failures)
  return (uniqueFailures, dedupedResults)

/-- Format and log the `#defeq_abuse` diagnostic report.
`kind` is `"tactic"` or `"command"`. -/
private def reportDefEqAbuse {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m]
    [MonadOptions m] (kind : String) (uniqueFailures : Array MessageData)
    (synthResults : Array (MessageData × Array MessageData)) : m Unit := do
  if !synthResults.isEmpty then
    -- Structured report: group by instance application
    let mut entries : Array MessageData := #[]
    for (app, failures) in synthResults do
      let failureList := joinSep
        (failures.toList.map fun f => m!"    {f}") "\n"
      entries := entries.push m!"  {app}\n{failureList}"
    let report := joinSep entries.toList "\n"
    logWarning
      m!"#defeq_abuse: {kind} fails with \
        `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
        The following synthesis applications fail due to transparency:\n{report}"
  else if uniqueFailures.isEmpty then
    logWarning
      m!"#defeq_abuse: {kind} fails with \
        `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
        Could not identify specific failing isDefEq checks from traces."
  else
    let failureList := joinSep
      (uniqueFailures.toList.map fun f => m!"  {f}") "\n"
    logWarning
      m!"#defeq_abuse: {kind} fails with \
        `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
        The following isDefEq checks are the root causes of the failure:\n{failureList}"

/--
`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting.

The tactic still executes (using the permissive setting if needed), so proofs remain valid
during debugging.
-/
elab (name := defeqAbuse) "#defeq_abuse " "in " tac:tactic : tactic => withMainContext do
    let s ← saveState
    let oldTraces ← getTraces
    -- Helper: run tactic with given options and tracing, capturing traces.
    let runAndCapture (strict : Bool) :
        TacticM (Except MessageData Unit × PersistentArray TraceElem) := do
      modifyTraces (fun _ => {})
      let result ← try
        withOptions (fun o =>
            (o.setBool `backward.isDefEq.respectTransparency strict)
              |>.setBool `trace.Meta.isDefEq true) do
          evalTactic tac
          pure (Except.ok ())
      catch
        | .internal id ref =>
          modifyTraces (fun _ => oldTraces)
          throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
      let traces ← getTraces
      modifyTraces (fun _ => oldTraces)
      return (result, traces)
    -- Pass 1: strict + tracing.
    -- If it succeeds, no abuse; if it fails, we already have the traces.
    let (strictResult, strictTraces) ← runAndCapture true
    s.restore (restoreInfo := true)
    match strictResult with
    | .ok () =>
      -- Tactic works fine with strict setting, nothing to report.
      logInfo
        "#defeq_abuse: tactic succeeds with \
          `backward.isDefEq.respectTransparency true`. No abuse detected."
      -- Re-run without tracing so proof state is updated cleanly.
      withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) do
        evalTactic tac
    | .error _ =>
      -- Pass 2: permissive + tracing.
      -- If it fails, command fails regardless; if it succeeds, we have the traces.
      let (permissiveResult, permTraces) ← runAndCapture false
      s.restore (restoreInfo := true)
      match permissiveResult with
      | .error _ =>
        logWarning
          "#defeq_abuse: tactic fails regardless of \
            `backward.isDefEq.respectTransparency` setting."
        -- Still run the tactic so the user sees the original error
        evalTactic tac
      | .ok () =>
        let strictMsgs := strictTraces.toArray.map (·.msg)
        let permMsgs := permTraces.toArray.map (·.msg)
        let (uniqueFailures, _) ← analyzeTraces strictMsgs permMsgs
        reportDefEqAbuse "tactic" uniqueFailures #[]
        -- Pass 3: run the tactic with permissive setting so it actually succeeds
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac

/--
`#defeq_abuse in cmd` runs `cmd` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the command succeeds with `false` but fails with `true`, it identifies the specific
synthesis applications and `isDefEq` checks that fail with the stricter setting.

This is useful for diagnosing `instance` declarations or other commands where type class synthesis
failures occur during elaboration rather than within a tactic.

The command is re-executed with the permissive setting so that it actually takes effect.
-/
syntax (name := defeqAbuseCmd) "#defeq_abuse " "in" command : command

elab_rules : command
  | `(command| #defeq_abuse in $cmd) => do
    let saved ← get
    -- Helper: run command with given scope options, capturing new messages.
    -- Returns (result, newMessages). elabCommand doesn't throw on synth failures,
    -- so we check the message log for errors.
    let runAndCapture (opts : Scope → Scope) :
        CommandElabM (Except MessageData Unit × List Message) := do
      let savedMsgCount := (← get).messages.toList.length
      let result ← try
        withScope opts do
          elabCommand cmd
          if (← get).messages.hasErrors then
            pure (Except.error m!"command produced errors")
          else
            pure (Except.ok ())
      catch
        | .internal id ref => throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
      let newMsgs := ((← get).messages.toList).drop savedMsgCount
      return (result, newMsgs)
    -- We set `Elab.async false` to force synchronous proof checking,
    -- otherwise `theorem` proofs are elaborated in a background task and errors
    -- won't appear in `messages` until after `elabCommand` returns.
    let traceOpts (strict : Bool) (scope : Scope) : Scope :=
      { scope with opts := (scope.opts.setBool `Elab.async false)
          |>.setBool `backward.isDefEq.respectTransparency strict
          |>.setBool `trace.Meta.isDefEq true
          |>.setBool `trace.Meta.synthInstance true }
    -- Pass 1: strict + tracing.
    -- If it succeeds, no abuse; if it fails, we already have the traces.
    let (strictResult, strictMsgs) ← runAndCapture (traceOpts true)
    set saved
    match strictResult with
    | .ok () =>
      logInfo "#defeq_abuse: command succeeds with \
        `backward.isDefEq.respectTransparency true`. No abuse detected."
      elabCommand cmd
    | .error _ =>
      -- Pass 2: permissive + tracing.
      -- If it fails, command fails regardless; if it succeeds, we have the traces.
      let (permissiveResult, permissiveMsgs) ← runAndCapture (traceOpts false)
      set saved
      match permissiveResult with
      | .error _ =>
        logWarning "#defeq_abuse: command fails regardless of \
          `backward.isDefEq.respectTransparency` setting."
        elabCommand cmd
      | .ok () =>
        let strictMsgData := strictMsgs.map (·.data) |>.toArray
        let permMsgData := permissiveMsgs.map (·.data) |>.toArray
        let (uniqueFailures, synthResults) ←
          analyzeTraces strictMsgData permMsgData (includeSynth := true)
        reportDefEqAbuse "command" uniqueFailures synthResults
        -- Pass 3: run the command with permissive setting so it actually takes effect
        withScope (fun scope =>
          { scope with opts := (scope.opts.setBool `Elab.async false)
              |>.setBool `backward.isDefEq.respectTransparency false }) do
          elabCommand cmd

end Mathlib.Tactic.DefEqAbuse

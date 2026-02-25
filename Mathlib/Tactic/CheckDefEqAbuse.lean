/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Init

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

open Lean Meta Elab Tactic Command

namespace Mathlib.Tactic.CheckDefEqAbuse

-- Note on string matching: Lean's `TraceData` has no structured success/failure field.
-- `withTraceNodeBefore` in Lean core prepends ✅/❌ emoji to the rendered header message,
-- and `Meta.synthInstance` "apply" nodes use the same trace class as other synthesis nodes.
-- String matching on the rendered header is the only way to determine trace node outcomes.

/-- Extract the instance name from a rendered `apply @Foo to Goal` trace header.
Returns the string between `"apply "` and `" to "`. -/
private def extractInstName (s : String) : String :=
  match s.splitOn "apply " with
  | [_, rest] => match rest.splitOn " to " with
    | name :: _ => name.trimAscii.toString
    | _ => s
  | _ => s

/-- Generic fold over a `MessageData` trace tree. Automatically recurses through `.compose`,
`.nest`, `.group`, `.tagged`, `.withContext`, `.withNamingContext`, delegating `.trace` nodes
to `onTrace`. The fourth argument to `onTrace` continues the fold through a child node. -/
private partial def foldTraces {α : Type} (onTrace : TraceData → MessageData → Array MessageData →
    (MessageData → BaseIO α) → BaseIO α) (combine : α → α → α) (empty : α)
    (msg : MessageData) : BaseIO α :=
  match msg with
  | .trace td header children =>
    onTrace td header children (foldTraces onTrace combine empty)
  | .compose a b => do
    return combine (← foldTraces onTrace combine empty a)
                   (← foldTraces onTrace combine empty b)
  | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m =>
    foldTraces onTrace combine empty m
  | _ => return empty

/-- Find the deepest failing `Meta.isDefEq` trace nodes (leaf failures).
Skips `onFailure` retry nodes and ignores ✅ branches (recovered failures aren't root causes). -/
private partial def findLeafFailures (msg : MessageData) : BaseIO (Array MessageData) :=
  foldTraces (fun td header children go => do
    if td.cls == `Meta.isDefEq.onFailure then return #[]
    if Name.isPrefixOf `Meta.isDefEq td.cls then
      let headerStr ← header.toString
      if headerStr.startsWith "❌" then
        let mut childFailures := #[]
        for child in children do
          childFailures := childFailures.append (← go child)
        -- Leaf failure: deepest ❌ node with no deeper ❌ children
        if childFailures.isEmpty then return #[header] else return childFailures
      else
        return #[]
    else
      let mut results := #[]
      for child in children do
        results := results.append (← go child)
      return results
  ) (· ++ ·) #[] msg

/-- Within a synthesis trace, find failing `apply @Instance to Goal` nodes
and their `isDefEq` leaf failures. -/
private partial def findSynthAppFailures (msg : MessageData) :
    BaseIO (Array (MessageData × Array MessageData)) :=
  foldTraces (fun td header children go => do
    if td.cls == `Meta.isDefEq.onFailure then return #[]
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.startsWith "❌" && headerStr.contains "apply" then
        let mut failures := #[]
        for child in children do
          failures := failures.append (← findLeafFailures child)
        if failures.isEmpty then
          -- No isDefEq failures here; recurse for sub-synthesis failures
          let mut results := #[]
          for child in children do
            results := results.append (← go child)
          return results
        else
          return #[(header, failures)]
      else
        let mut results := #[]
        for child in children do
          results := results.append (← go child)
        return results
    let mut results := #[]
    for child in children do
      results := results.append (← go child)
    return results
  ) (· ++ ·) #[] msg

/-- Find top-level synthesis failures and their `isDefEq` root causes.
Only enters failing synthesis nodes to avoid reporting recovered sub-attempts. -/
private partial def findSynthFailures (msg : MessageData) :
    BaseIO (Array (MessageData × Array MessageData)) :=
  foldTraces (fun td header children go => do
    if td.cls == `Meta.isDefEq.onFailure then return #[]
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.startsWith "❌" then
        let mut results := #[]
        for child in children do
          results := results.append (← findSynthAppFailures child)
        return results
      else
        return #[]
    -- Skip isDefEq/synthInstance subtrees that aren't top-level synthesis
    if !Name.isPrefixOf `Meta.isDefEq td.cls &&
        !Name.isPrefixOf `Meta.synthInstance td.cls then
      let mut results := #[]
      for child in children do
        results := results.append (← go child)
      return results
    return #[]
  ) (· ++ ·) #[] msg

/-- Collect instance names from successful `apply @Instance to Goal` trace nodes. -/
private partial def findSynthSuccessApps (msg : MessageData) : BaseIO (Std.HashSet String) :=
  foldTraces (fun td header children go => do
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.contains "apply" && !headerStr.startsWith "❌" then
        let mut result : Std.HashSet String := {}
        result := result.insert (extractInstName headerStr)
        for child in children do
          result := result.union (← go child)
        return result
      else
        let mut result : Std.HashSet String := {}
        for child in children do
          result := result.union (← go child)
        return result
    let mut result : Std.HashSet String := {}
    for child in children do
      result := result.union (← go child)
    return result
  ) (·.union ·) {} msg

/-- Deduplicate an array of `MessageData` by rendering to string. -/
private def dedup (failures : Array MessageData) : BaseIO (Array MessageData) := do
  let mut seen : Std.HashSet String := {}
  let mut unique : Array MessageData := #[]
  for failure in failures do
    let s ← failure.toString
    unless seen.contains s do
      seen := seen.insert s
      unique := unique.push failure
  return unique

/--
`#defeq_abuse in tac` runs `tac` with `backward.isDefEq.respectTransparency` both `true` and
`false`. If the tactic succeeds with `false` but fails with `true`, it identifies the specific
`isDefEq` checks that fail with the stricter setting.

The tactic still executes (using the permissive setting if needed), so proofs remain valid
during debugging.
-/
elab (name := defeqAbuse) "#defeq_abuse " "in " tac:tactic : tactic => withMainContext do
    let tk ← getRef
    let s ← saveState
    -- First, try with respectTransparency true (the strict/new default)
    let strictResult ← try
      withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency true) do
        evalTactic tac
        pure (Except.ok ())
    catch
      | .internal id ref => throw (.internal id ref)
      | e => pure (Except.error e.toMessageData)
    match strictResult with
    | .ok () =>
      -- Tactic works fine with strict setting, nothing to report.
      -- The tactic has already been executed, so proof state is updated.
      logInfoAt tk
        "#defeq_abuse: tactic succeeds with \
          `backward.isDefEq.respectTransparency true`. No abuse detected."
    | .error _ =>
      s.restore
      -- Try with respectTransparency false (the permissive/old setting)
      let permissiveResult ← try
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac
          pure (Except.ok ())
      catch
        | .internal id ref => throw (.internal id ref)
        | e => pure (Except.error e.toMessageData)
      match permissiveResult with
      | .error _ =>
        s.restore
        logWarningAt tk
          "#defeq_abuse: tactic fails regardless of \
            `backward.isDefEq.respectTransparency` setting."
        -- Still run the tactic so the user sees the original error
        evalTactic tac
      | .ok () =>
        s.restore
        -- Now we know: strict fails, permissive works.
        -- Run with strict + tracing to capture the failure details.
        let oldTraces ← getTraces
        modifyTraces (fun _ => {})
        _ ← try
          withOptions (fun o =>
              (o.setBool `backward.isDefEq.respectTransparency true)
                |>.setBool `trace.Meta.isDefEq true) do
            evalTactic tac
            pure (Except.ok ())
        catch
          | .internal id ref =>
            modifyTraces (fun _ => oldTraces)
            throw (.internal id ref)
          | e => pure (Except.error e.toMessageData)
        let failTraces ← getTraces
        modifyTraces (fun _ => oldTraces)
        s.restore
        -- Find leaf failures in the trace tree
        let mut leafFailures : Array MessageData := #[]
        for trace in failTraces do
          leafFailures := leafFailures ++ (← findLeafFailures trace.msg)
        let uniqueFailures ← dedup leafFailures
        if uniqueFailures.isEmpty then
          logWarningAt tk
            m!"#defeq_abuse: tactic fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              Could not identify specific failing isDefEq checks from traces."
        else
          let failureList := MessageData.joinSep
            (uniqueFailures.toList.map fun f => m!"  {f}") "\n"
          logWarningAt tk
            m!"#defeq_abuse: tactic fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              The following isDefEq checks are the root causes of the failure:\n{failureList}"
        -- Run the tactic with permissive setting so it actually succeeds
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
  | `(command| #defeq_abuse%$tk in $cmd) => do
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
    let traceOpts (strict : Bool) (scope : Scope) : Scope :=
      { scope with opts := (scope.opts.setBool `backward.isDefEq.respectTransparency strict)
          |>.setBool `trace.Meta.isDefEq true
          |>.setBool `trace.Meta.synthInstance true }
    -- Pass 1: strict + tracing.
    -- If it succeeds, no abuse; if it fails, we already have the traces.
    let (strictResult, strictMsgs) ← runAndCapture (traceOpts true)
    set saved
    match strictResult with
    | .ok () =>
      logInfoAt tk "#defeq_abuse: command succeeds with \
        `backward.isDefEq.respectTransparency true`. No abuse detected."
      elabCommand cmd
    | .error _ =>
      -- Pass 2: permissive + tracing.
      -- If it fails, command fails regardless; if it succeeds, we have the traces.
      let (permissiveResult, permissiveMsgs) ← runAndCapture (traceOpts false)
      set saved
      match permissiveResult with
      | .error _ =>
        logWarningAt tk "#defeq_abuse: command fails regardless of \
          `backward.isDefEq.respectTransparency` setting."
        elabCommand cmd
      | .ok () =>
        -- Strict fails, permissive works. Analyze traces from passes 1 and 2.
        -- Collect instance names that SUCCEED with permissive setting.
        -- Only strict-failing applications that succeed permissively are due
        -- to the transparency change.
        let mut permissiveSuccessApps : Std.HashSet String := {}
        for m in permissiveMsgs do
          permissiveSuccessApps := permissiveSuccessApps.union
            (← findSynthSuccessApps m.data)
        -- Find synthesis failures with isDefEq root causes (strict only)
        let mut synthResults : Array (MessageData × Array MessageData) := #[]
        for m in strictMsgs do
          synthResults := synthResults.append (← findSynthFailures m.data)
        -- Filter to only applications that succeed with permissive transparency.
        let filteredResults ← synthResults.filterM fun (app, _) => do
          return permissiveSuccessApps.contains (extractInstName (← app.toString))
        if filteredResults.isEmpty then
          -- Fall back to flat isDefEq leaf failures
          let mut leafFailures : Array MessageData := #[]
          for m in strictMsgs do
            leafFailures := leafFailures.append (← findLeafFailures m.data)
          let uniqueFailures ← dedup leafFailures
          if uniqueFailures.isEmpty then
            logWarningAt tk
              m!"#defeq_abuse: command fails with \
                `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
                Could not identify specific failing isDefEq checks from traces."
          else
            let failureList := MessageData.joinSep
              (uniqueFailures.toList.map fun f => m!"  {f}") "\n"
            logWarningAt tk
              m!"#defeq_abuse: command fails with \
                `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
                The following isDefEq checks are the root causes of the failure:\n{failureList}"
        else
          -- Format structured report: group by instance application
          let mut entries : Array MessageData := #[]
          for (app, failures) in filteredResults do
            let uniqueFailures ← dedup failures
            let failureList := MessageData.joinSep
              (uniqueFailures.toList.map fun f => m!"    {f}") "\n"
            entries := entries.push m!"  {app}\n{failureList}"
          let report := MessageData.joinSep entries.toList "\n"
          logWarningAt tk
            m!"#defeq_abuse: command fails with \
              `backward.isDefEq.respectTransparency true` but succeeds with `false`.\n\
              The following synthesis applications fail due to transparency:\n{report}"
        -- Pass 3: run the command with permissive setting so it actually takes effect
        withScope (fun scope =>
          { scope with opts := scope.opts.setBool `backward.isDefEq.respectTransparency false }) do
          elabCommand cmd

end Mathlib.Tactic.CheckDefEqAbuse

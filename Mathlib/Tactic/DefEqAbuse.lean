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

**WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking changes to
transparency handling (associated with `backward.isDefEq.respectTransparency`). Its syntax may
change at any time, and it may not behave as expected. Please report unexpected behavior
[on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

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

meta section

open Lean MessageData Meta Elab Tactic Command

namespace Lean.MessageData

/- TODO: this section should be moved to `Lean.MessageData.Trace` when finalized and made public. -/

/-- A return value for functions called by traversals of `MessageData`. May either descend into
children or ascend immediately (skipping children), optionally including a value accumulated by the
traversal in both cases. -/
inductive VisitStep (α) where
/-- Descends through the `MessageData`, visiting all children. If the argument `butFirst` is given
as `some a` (`none` by default), starts with `a`, and combines any values produced by children with
this value. -/
| descend (butFirst : Option α := none)
/-- Skips visiting children, and ascends to the parent, returning the value given in `returning`
(if any). -/
| ascend (returning : Option α := none)

variable {m : Type → Type} [Monad m] {α : Type}

/-- Collect and combine values of type `α` produced by visiting all trace nodes in a `MessageData`
tree.

Automatically recurses through structural wrappers, invoking `onTrace` only for
`.trace` nodes. The `onTrace` callback receives the arguments of `.trace`:
- the `TraceData` (class name, timing, etc.)
- the trace node's header message
- the trace node's child messages

Each call to `onTrace` is expected to produce either a `descend`, in which case the children of the
trace nodes will be visited, or an `ascend`, in which case they will not. Both may take an argument
`butFirst := some a`, which will cause `a` to be `combine`d into the accumulated value.

We assume `x = combine empty x = combine x empty`. `empty` is attempted to be synthesized as the
`EmptyCollection`, and `combine` is attempted to be synthesized first via the notation `(· ++ ·)`
then via `(· ∪ ·)` as a fallback.

Note that the children may be visited manually via a recursive call to `collectWith` or
`collectWithAndAscend`.

Note: `.ofLazy` nodes are skipped (return `empty`) because they contain unevaluated
formatting thunks, not trace tree structure. This is consistent with `hasTag`
in `Lean.Message` which also skips `.ofLazy`. -/
partial def visitTraceNodesM (msg : MessageData)
    (onTrace : TraceData → MessageData → Array MessageData → m (MessageData.VisitStep α))
    (empty : α := by exact {}) (combine : α → α → α := by first | exact (· ++ ·) | exact (· ∪ ·)) :
    m α :=
  go msg
where
  /-- The continuation for `visitTraceNodesM`; this is mainly for readability (takes only one
  argument in source). -/
  go : MessageData → m α
    | .trace td header children => do
      match ← onTrace td header children with
      | .descend a? => do
        let mut result := a?.getD empty
        for child in children do
          result := combine result (← go child)
        return result
      | .ascend a? => return a?.getD empty
    | .compose a b => return combine (← go a) (← go b)
    | .nest _ m | .group m | .tagged _ m | .withContext _ m | .withNamingContext _ m => go m
    | .ofLazy _ _ | .ofWidget _ _ | .ofGoal _ | .ofFormatWithInfos _ => return empty

/-- Convenience wrapper which accumulates the results of `visitM` across `arr`, attempting to
produce `empty` and `combine` from `{}` and `(· ++ ·)` or `(· ∪ ·)`. -/
@[inline] def visitWithM {β} (arr : Array β) (visitM : β → m α)
    (empty : α := by exact {}) (combine : α → α → α := by first | exact (· ++ ·) | exact (· ∪ ·)) :
    m α :=
  arr.foldlM (init := empty) fun acc msg => return combine acc (← visitM msg)

/-- Convenience wrapper which accumulates the results of `visitM` across `arr`, attempting to
produce `empty` and `combine` from `{}` and `(· ++ ·)` or `(· ∪ ·)`, then `.ascend`s with the result
(if any). This effectively replaces a return value of `.descend`. -/
@[inline] def visitWithAndAscendM {β} (arr : Array β) (visitM : β → m α)
    (empty : α := by exact {}) (combine : α → α → α := by first | exact (· ++ ·) | exact (· ∪ ·)) :
    m (VisitStep α) := do
  if arr.isEmpty then return .ascend else
    return .ascend <|← visitWithM arr visitM empty combine

/-- Recursively modify the pp options captured in `MessageData.withContext` nodes.
Used to re-render `X =?= X` failures with `pp.universes` or `pp.explicit` to show
the difference between LHS and RHS without re-running the full analysis. -/
partial def withPPOptions (msg : MessageData) (modify : Options → Options) : MessageData :=
  match msg with
  | .withContext ctx d =>
    .withContext { ctx with opts := modify ctx.opts } (withPPOptions d modify)
  | .compose a b => .compose (withPPOptions a modify) (withPPOptions b modify)
  | .nest n m => .nest n (withPPOptions m modify)
  | .group m => .group (withPPOptions m modify)
  | .tagged t m => .tagged t (withPPOptions m modify)
  | .withNamingContext nc m => .withNamingContext nc (withPPOptions m modify)
  | .trace td header children =>
    .trace td (withPPOptions header modify) (children.map (withPPOptions · modify))
  | .ofWidget w m => .ofWidget w (withPPOptions m modify)
  | other@(.ofLazy _ _)
  | other@(.ofFormatWithInfos _)
  | other@(.ofGoal _) => other

end Lean.MessageData

namespace Mathlib.Tactic.DefEqAbuse

/-- Only applies `f` to `Meta.isDefEq` trace nodes. Skips `Meta.isDefEq.onFailure` nodes. -/
@[inline] def onlyOnDefEqNodes {m} [Monad m] {α}
    (f : TraceData → MessageData → Array MessageData → m (VisitStep α)) :
    TraceData → MessageData → Array MessageData → m (VisitStep α) :=
  fun td header children => do
    if td.cls == `Meta.isDefEq.onFailure then return .ascend
    unless (`Meta.isDefEq).isPrefixOf td.cls do return .descend
    f td header children

/-- Find the deepest failing `Meta.isDefEq` trace nodes (leaf failures).
Skips `onFailure` retry nodes and ignores ✅️ branches (recovered failures aren't root causes).
Note: status is currently determined by parsing emoji from the rendered header string.
Once https://github.com/leanprover/lean4/pull/12698 is available, use `td.result?` instead. -/
partial def findLeafFailures (msg : MessageData) : BaseIO (Array MessageData) :=
  msg.visitTraceNodesM <| onlyOnDefEqNodes fun td header children => do
    unless traceResultOf (← header.toString) matches some .failure do
      return .ascend
    let childFailures ← visitWithM children findLeafFailures
    -- Leaf failure: deepest `❌️` node with no deeper `❌️` children
    return .ascend <| if childFailures.isEmpty then #[header] else childFailures

/-- Collect rendered check strings from `Meta.isDefEq` trace nodes matching a status predicate.
Returns a `HashSet` of emoji-stripped header strings. -/
partial def collectIsDefEqChecks (pred : TraceResult → Bool)
    (msg : MessageData) : BaseIO (Std.HashSet String) :=
  msg.visitTraceNodesM <| onlyOnDefEqNodes fun td header children => do
    let headerStr ← header.toString
    if let some status := traceResultOf headerStr then
      if pred status then
        return .descend (butFirst := some {stripTraceResultPrefix headerStr})
    return .descend

/-- Find the deepest `Meta.isDefEq` transition points: nodes that fail in the strict trace
but whose check string appears as a success in the permissive trace and does NOT also appear
as a failure in the permissive trace (which would indicate the check is context-dependent
rather than transparency-dependent).
A "deepest transition point" has no descendant transition points.
Falls back to `findLeafFailures` behavior when `permSuccesses` is empty. -/
partial def findTransitionFailures (permSuccesses : Std.HashSet String)
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
partial def findSynthAppFailures (permSuccesses permFailures : Std.HashSet String)
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
partial def findSynthFailures (permSuccesses permFailures : Std.HashSet String)
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
check can be replaced with ``td.cls == `Meta.synthInstance.apply``. -/
partial def findSynthSuccessApps (msg : MessageData) : BaseIO (Std.HashSet String) :=
  msg.visitTraceNodesM fun td header children => do
    if td.cls == `Meta.synthInstance then
      let headerStr ← header.toString
      if headerStr.contains "apply" && traceResultOf headerStr == some .success then
        return .descend (butFirst := some {extractInstName headerStr})
    return .descend

/-- Analyze strict and permissive trace messages to find isDefEq transition failures
and (optionally) synthesis-grouped failures.
Returns `(flatFailures, synthGroupedFailures)`. -/
def analyzeTraces (strictMsgs permMsgs : Array MessageData) (includeSynth : Bool := false) :
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

/-- Check whether a rendered isDefEq check string has syntactically identical LHS and RHS
(e.g. `"❌️ ⊤ =?= ⊤"` or `"Quiver C =?= Quiver C"`).
Comparison is whitespace-insensitive to handle cases where LHS and RHS are semantically identical
but rendered with different line breaks or spacing.
TODO: once https://github.com/leanprover/lean4/pull/12698 is available, refactor to use
`TraceData.result?` and compare the LHS/RHS `Expr`s structurally instead of string-matching. -/
private def isIdenticalSidesStr (raw : String) : Bool :=
  if let [lhsRaw, rhs] := raw.splitOn " =?= " then
    -- Strip the leading status emoji/word (first whitespace-delimited token).
    let lhs := match lhsRaw.splitOn " " with
      | _ :: rest => " ".intercalate rest
      | _ => lhsRaw
    -- Compare up to whitespace so that line-break differences don't cause false negatives.
    let tokenize (s : String) : List String :=
      (s.split Char.isWhitespace).toList.map (·.toString) |>.filter (· ≠ "")
    tokenize lhs == tokenize rhs
  else false

/-- PP option escalation levels for disambiguating `X =?= X` failures.
Each level adds more detail to pretty-printed expressions.
We prefer symmetric options (`pp.universes`, `pp.explicit`) over `pp.analyze`,
which is context-dependent and can add annotations to only one side. -/
private def ppEscalations : List (Options → Options) :=
  [ fun o => o.setBool `pp.universes true
  , fun o => o.setBool `pp.explicit true
  ]

/-- For failures with syntactically identical LHS and RHS (e.g. `⊤ =?= ⊤`), re-render with
progressively more verbose pp settings to disambiguate. This modifies only the rendering
of the `MessageData` (via `withPPOptions`), not the analysis — the captured `MetavarContext`
and trace structure are preserved, so transition-point detection remains correct. -/
def disambiguateFailures (failures : Array MessageData) : BaseIO (Array MessageData) :=
  failures.mapM fun f => do
    unless isIdenticalSidesStr (← f.toString) do return f
    for ppLevel in ppEscalations do
      let escalated := f.withPPOptions ppLevel
      unless isIdenticalSidesStr (← escalated.toString) do return escalated
    return f

/-- Format and log the `#defeq_abuse` diagnostic report.
`kind` is `"tactic"` or `"command"`. -/
def reportDefEqAbuse {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m]
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

/-- Collect candidate semireducible definition names by transitively following declaration values
reachable from `roots`, up to a bounded depth. -/
def collectCandidates (env : Environment) (roots : Array Name) : Array Name := Id.run do
  let mut visited : NameSet := {}
  let mut queue := roots
  let mut candidates : Array Name := #[]
  for _ in (0 : Nat)...6 do -- depth limit
    if queue.isEmpty then break
    let current := queue
    queue := #[]
    for name in current do
      if visited.contains name then continue
      visited := visited.insert name
      if let some info := env.find? name then
        if wasOriginallyDefn env name && getReducibilityStatusCore env name == .semireducible then
          candidates := candidates.push name
        -- Only `defs`, `theorem`s and `opaque`s can have values, and we only care about the first.
        if let .defnInfo { value .. } := info then
          for c in value.getUsedConstants do
            if !visited.contains c then
              queue := queue.push c
  return candidates

/-- Temporarily mark constants as `@[implicit_reducible]`, run an action, then restore all state.

The full tactic state (which includes the environment carrying recuibility marks) are saved before
the marks are applied and restored via `finally`, so this helper is self-contained: callers do not
need additional save/restore wrappers. -/
def withTempImplicitReducible {α : Type} (names : Array Name) (k : TacticM α) : TacticM α := do
  let s ← saveState
  try
    for name in names do setReducibilityStatus name .implicitReducible
    k
  finally
    s.restore (restoreInfo := true)

/-- Temporarily mark constants as `@[implicit_reducible]`, run an action, then restore all state.

Command-level variant: the full `CommandElabM` state (which includes the environment) is saved
before the marks are applied and restored via `finally`, so this helper is self-contained. -/
def withTempImplicitReducibleCmd {α : Type} (names : Array Name)
    (k : CommandElabM α) : CommandElabM α := do
  let saved ← get
  try
    for name in names do setReducibilityStatus name .implicitReducible
    k
  finally
    set saved

/-- Given a function `succeeds : Array Name → m Bool` and an initial array of `candidates` such
that `succeeds candidates` is `true` (returning `none` if this is not the case), tries removing
elements from `candidates` in order such that the resulting array still `succeeds`. Sorts the
result.

This minimization may not be unique. It also is only minimal under the assumption that removing a
later element from the array cannot cause an earlier element to become removable. -/
def minimizeCandidates {m} [Monad m] (succeeds : Array Name → m Bool) (candidates : Array Name) :
    m (Option (Array Name)) := do
  unless ← succeeds candidates do return none
  let mut minimal := candidates
  for name in minimal do
    let without := minimal.filter (· != name)
    if ← succeeds without then minimal := without
  return minimal.qsort Name.lt

/-- Try to find a (possibly non-unique) minimal set of semireducible constants that, when marked
`@[implicit_reducible]`, make the tactic succeed with `backward.isDefEq.respectTransparency true`.

Collects candidates by transitively following definition values reachable from the goal type,
filtering to semireducible definitions. Then verifies and minimizes the set by greedy removal.
Greedy removal is order-dependent, so the result may not be the unique smallest such set. -/
def suggestAnnotationsTac (tac : Syntax) : TacticM (Option (Array Name)) := do
  let goalType ← getMainTarget
  let candidates := collectCandidates (← getEnv) goalType.getUsedConstants
  if candidates.isEmpty then return none
  let succeedsWith (names : Array Name) : TacticM Bool :=
    withTempImplicitReducible names do withCurrHeartbeats do
      withOptions (·.setBool `backward.isDefEq.respectTransparency true) do
        try
          Core.resetMessageLog
          Term.withoutErrToSorry <| evalTactic tac
          notM MonadLog.hasErrors
        catch _ => pure false
  minimizeCandidates succeedsWith candidates

/-- Try to find a (possibly non-unique) minimal set of semireducible constants that, when marked
`@[implicit_reducible]`, make the command succeed with `backward.isDefEq.respectTransparency true`.
Greedy removal is order-dependent, so the result may not be the unique smallest such set. -/
def suggestAnnotationsCmd (cmd : Syntax) : CommandElabM (Option (Array Name)) := do
  -- Collect roots from the command's syntax resolution
  let env ← getEnv
  -- Extract constant names mentioned in the command syntax by elaborating once permissively
  -- and checking what constants appear in the resulting environment additions.
  -- As a heuristic, use all constants from the new declarations.
  let saved ← get
  let roots ← try
    withScope (fun scope =>
      { scope with opts := scope.opts.setBool `Elab.async false
          |>.setBool `backward.isDefEq.respectTransparency false }) do
      elabCommand cmd
      let newEnv ← getEnv
      let mut names : NameSet := {}
      -- Collect constants from any new declarations added by this command
      for (name, info) in newEnv.constants.map₂ do
        if !env.constants.map₂.contains name then
          names := names ∪ info.getUsedConstantsAsSet
      return names
  catch _ => pure {}
  set saved
  let candidates := collectCandidates (← getEnv) roots.toArray
  if candidates.isEmpty then return none
  let succeedsWith (names : Array Name) : CommandElabM Bool :=
    withTempImplicitReducibleCmd names do
      withScope (fun scope =>
        { scope with opts := scope.opts.setBool `Elab.async false
            |>.setBool `backward.isDefEq.respectTransparency true }) do
        try
          elabCommand cmd
          notM MonadLog.hasErrors
        catch _ => return false
  minimizeCandidates succeedsWith candidates

/-- Format the annotation workaround as a Lean code snippet. -/
def formatAnnotations (names : Array Name) : MessageData :=
  let namesList := joinSep (names.toList.map (m!"  {.ofConstName · (fullNames := true)}")) "\n"
  m!"set_option allowUnsafeReducibility true\nattribute [implicit_reducible]\n{namesList}"

/-- Log annotation suggestions as info. -/
def logAnnotationSuggestions {m : Type → Type} [Monad m] [MonadLog m] [AddMessageContext m]
    [MonadOptions m] (names : Option (Array Name)) : m Unit := do
  let some names := names | return
  if names.isEmpty then return
  logInfo m!"Workaround: the following `@[implicit_reducible]` annotations (a possibly \
    non-unique minimal set) would paper over this problem, but the real issue is likely a leaky \
    instance somewhere.\n\n\
    {formatAnnotations names}"

/--
> **WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking
changes to transparency handling. Its syntax may change at any time, and it may not behave as
expected. Please report unexpected behavior [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

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
      try
        let result ← try
          withOptions (fun o =>
              (o.setBool `backward.isDefEq.respectTransparency strict)
                |>.setBool `trace.Meta.isDefEq true) do
            evalTactic tac
            pure (Except.ok ())
        catch e => pure (Except.error e.toMessageData)
        let traces ← getTraces
        return (result, traces)
      finally
        modifyTraces (fun _ => oldTraces)
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
        let disambiguated ← disambiguateFailures uniqueFailures
        reportDefEqAbuse "tactic" disambiguated #[]
        -- Attempt to find minimal @[implicit_reducible] workaround
        try logAnnotationSuggestions (← suggestAnnotationsTac tac) catch _ => pure ()
        -- Pass 3: run the tactic with permissive setting so it actually succeeds
        withOptions (fun o => o.setBool `backward.isDefEq.respectTransparency false) do
          evalTactic tac

/--
> **WARNING:** `#defeq_abuse` is an experimental tool intended to assist with breaking
changes to transparency handling. Its syntax may change at any time, and it may not behave as
expected. Please report unexpected behavior [on Zulip](https://leanprover.zulipchat.com/#narrow/channel/113488-general/topic/backward.2EisDefEq.2ErespectTransparency/with/575685551).

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
      catch e => pure (Except.error e.toMessageData)
      let newMsgs := ((← get).messages.toList).drop savedMsgCount
      return (result, newMsgs)
    -- We set `Elab.async false` to force synchronous proof checking,
    -- otherwise `theorem` proofs are elaborated in a background task and errors
    -- won't appear in `messages` until after `elabCommand` returns.
    -- TODO: wait on all of the tasks instead of disabling async entirely.
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
        let disambiguatedFailures ← disambiguateFailures uniqueFailures
        let disambiguatedSynth ← synthResults.mapM fun (app, failures) => do
          return (app, ← disambiguateFailures failures)
        reportDefEqAbuse "command" disambiguatedFailures disambiguatedSynth
        -- Attempt to find minimal @[implicit_reducible] workaround
        try logAnnotationSuggestions (← suggestAnnotationsCmd cmd) catch _ => pure ()
        -- Pass 3: run the command with permissive setting so it actually takes effect
        withScope (fun scope =>
          { scope with opts := scope.opts.setBool `backward.isDefEq.respectTransparency false }) do
          elabCommand cmd

end Mathlib.Tactic.DefEqAbuse

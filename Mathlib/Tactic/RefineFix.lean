/-
Copyright (c) 2023 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean
import Std.Tactic.TryThis
import Mathlib.Lean.CoreM
import Mathlib.Lean.Elab.Term
import Mathlib.Lean.Elab.Tactic.ElabTerm
import Mathlib.Util.Syntax

/-! # `refine?`

This file implements `refine? e`, which suggests which natural holes in `e` must be replaced with
`?_` in order to make `refine e` work.

`refine?` works syntactically: only explicit `_`'s are eligible for replacement with `?_`. As such,
implicit and instance arguments may cause `refine?` to fail to generate a suggestion where
`refine'` would succeed.

`refine? e` behaves like `refine e'` where `e'` is the "fixed" version of `e`, even when the
suggestion has not yet been applied. If `refine e'` logs any new errors or fails, no suggestion is
made.

## Implementation notes

### Core logic

Instead of using the infotree to determine which `_`'s were assigned, we use `ErrorInfo`s in order
to better replicate the logic of `refine`. `logUnassignedUsingErrorInfos` is modified to replace
`_`'s in the syntax with `?_`'s instead of logging errors in those cases.

Note: we assume that if the range of an `MVarId`'s `ref` lies within the range of the input syntax,
then the replacement will be successful.

Note that we look for original `_`'s in syntax, not for `ErrorInfos` with `kind := .hole`, as
sometimes `_` can be used in situations in which a different error is registered (such as the type
of `let` bindings).

### Elaboration & state management

Unlike non-suggestion tactics, `refine?` must elaborate the syntax twice: once to expose the
natural goals and check which must be replaced, and once with the modified syntax. The outcomes
here differ because `_`-holes are elaborated differently than `?`-holes, resulting in different
expressions in the infoview.

This means that we want to perform the first elaboration without modifying the `TacticM` state,
including without modifying or saving the infotrees (lest we have duplicated hovers).

## TODO

* We may be able to get away with replacing fewer `_`'s with `?_`s than we currently do. Currently,
  all `_`'s which depend on some unassigned `_` are replaced with `?_`. This would increase
  readability, but would not greatly change functionality, as `?_`'s are still assigned by `refine`
  during `elabTermEnsuringType stx (← getMainTarget)` (which uses `withAssignableSyntheticOpaque`
  during its `isDefEq` check). It might, however, alter elaboration slightly.

-/

open Lean Meta Elab Tactic Term Std.Tactic.TryThis

/-- Determine if syntax is a hole (`_`) present in original syntax. -/
private def Lean.Syntax.isOriginalHole : Syntax → Bool
  | .node _ ``Lean.Parser.Term.hole #[.atom (.original ..) _] => true
  | _ => false

/-- Replaces unassigned `_` (not `?*`) in `stx` with `?_`. Returns the new syntax as well as a
`Bool` which is `true` iff other errors were encountered.

This function is closely modeled after `logUnassignedUsingErrorInfos` so as to capture the behavior
of `refine` (which employs that function) accurately.

As part of the core change in its functionality, it does not log errors for unassigned `_`'s which
were successfully replaced by `?_`.

Also, unlike `logUnassignedUsingErrorInfos`, it does not prevent error logging if
`← MonadLog.hasErrors` is `true`. (This winds up not mattering in its application in `refine?`, as
we rewind the state anyway.)
-/
private def replaceUnassignedHolesUsingErrorInfos {kinds} (pendingMVarIds : Array MVarId)
    (stx : TSyntax kinds) (extraMsg? : Option MessageData := none) :
    TermElabM (TSyntax kinds × Bool) := do
  if pendingMVarIds.isEmpty then
    return (stx, false)
  else
    /- `logUnassignedUsingMvarErrorInfos` only records new errors if there are no existing errors.
        We don't restrict ourselves in that way here. -/
    let mut newStx := stx
    let mut hasNewErrors := false
    let mut alreadyVisited : MVarIdSet := {}
    let mut errors : Array MVarErrorInfo := #[]
    for (_, mvarErrorInfo@{ mvarId, ref, .. }) in (← get).mvarErrorInfos do
      unless alreadyVisited.contains mvarId do
        alreadyVisited := alreadyVisited.insert mvarId
        /- The metavariable `mvarErrorInfo.mvarId` may have been assigned or
           delayed assigned to another metavariable that is unassigned. -/
        let mvarDeps ← getMVars (.mvar mvarId)
        if mvarDeps.any pendingMVarIds.contains then
          /- Note that we check that the `mvarId`'s `ref` is both (1) a (non-`?`) hole and (2)
          canonical syntax included in the range of `stx`. -/
          if ref.isOriginalHole && stx.includes ref then
            -- We assume that the replacement was successful.
            -- TODO: introduce `replaceM'` to be more careful.
            newStx ← newStx.replaceM fun stx => do
              if stx.isOriginalHole && stx.isEqByRange ref then
                withRef stx `(?_)
              else
                pure none
          else
            errors := errors.push mvarErrorInfo
            hasNewErrors := true
    -- We technically don't need to log errors in our current implementation of `refine?`.
    -- But for the sake of maintainability, we do what you'd "expect" to do here nonetheless.
    for error in errors do
      error.mvarId.withContext do
        error.logError extraMsg?
    return (newStx, hasNewErrors)

/-! ## `refine?` tactic -/

/--
`refine? e` replaces all unsynthesized natural holes (`_`) in `e` with `?_`, then suggests
`refine e'` (where `e'` is the modified syntax).

Note that `refine? e` does not handle implicit or instance arguments that do not appear as `_` in
`e`, and will still fail if they cannot be synthesized. To create goals for implicit or instance
arguments, consider using `refine'`.

`refine? e` acts like `refine e'` even when the suggestion has not yet been applied, and the tactic
state visible after `refine? e` will be the same as the tactic state after `refine e'`.
-/
syntax (name := refine?) "refine? " term : tactic

elab_rules : tactic
| `(tactic|refine?%$r $t:term) => withMainContext do
  let (newStx, _) ← Term.withoutModifyingState (restoreInfo := true) do
    let (_, mvars) ← elabTermWithHoles' t (← getMainTarget) (allowedHoles := .allowNaturalHoles)
    let naturalMVars ← mvars.toArray.filterM fun mvarId => return (← mvarId.getKind).isNatural
    replaceUnassignedHolesUsingErrorInfos naturalMVars t
  let newStx ← `(tactic|refine%$r $newStx)
  let (_, hasNewErrors) ← hasNewErrors <| evalTactic newStx
  -- Only suggest a replacement if it won't cause errors.
  unless hasNewErrors do
    addSuggestion (← getRef) newStx.unsetOriginalTrailing

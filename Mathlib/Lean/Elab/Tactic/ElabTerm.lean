/-
Copyright (c) 2023 Thomas R. Murrills. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas R. Murrills
-/
import Lean

/-!
# Additions to `Lean.Elab.Tactic.ElabTerm`
-/

namespace Lean.Elab.Tactic

open Lean Meta Elab Tactic

/-- Config option for `withCollectingNewGoalsFrom'` and `elabTermWithHoles'`: determines whether to
`.allowNaturalHoles`, `.allowNaturalHolesAsSyntheticOpaque`, or `disallowNaturalHoles`. -/
inductive AllowedHoles where
  /-- Fail if any natural holes are not assigned. This is the behavior used by `refine`. -/
  | disallowNaturalHoles
  /-- Allow natural holes (`_`), but elaborate them as `.syntheticOpaque` holes.
    This is the behavior used by `refine'`. -/
  | allowNaturalHolesAsSyntheticOpaque
  /-- Allow natural holes. -/
  | allowNaturalHoles
deriving Repr, DecidableEq

/--
  Like `withCollectingNewGoalsFrom`, execute `k`, and collect new "holes" appearing in the resulting
  expression. However, this function differs in two key respects:

  1. If `allowedHoles := .allowNaturalHoles`, preserve the `MetavarKind` of each metavariable (in
    contrast, when `allowNaturalHoles := true`, `withCollectingNewGoalsFrom` turns natural holes
    into synthetic opaque holes via `holesAsSyntheticOpaque := true` and uses
    `withAssignableSyntheticOpaque` to assign them.
  2. If `tagSuffix := none`, we do not tag all untagged goals.

  Note that `allowedHoles` can take three values: `.disallowNaturalHoles` (which replicates
  `refine` behavior), `.allowNaturalHolesAsSyntheticOpaque` (which replicates `refine'` behavior),
  and `.allowNaturalHoles`, which preserves `MetavarKind`s as described in (1).
-/
-- See `withCollectingNewGoalsFrom` for more detailed code comments.
def withCollectingNewGoalsFrom' (k : TacticM Expr) (tagSuffix : Option Name := none)
    (allowedHoles : AllowedHoles := .disallowNaturalHoles) : TacticM (Expr × List MVarId) :=
  match allowedHoles with
  | .allowNaturalHolesAsSyntheticOpaque => withTheReader Term.Context
    (fun ctx => { ctx with holesAsSyntheticOpaque := ctx.holesAsSyntheticOpaque || true }) do
      withAssignableSyntheticOpaque go
  | _ => go
where
  /-- The core of `withCollectingNewGoalsFrom'`. -/
  go := do
    let mvarCounterSaved := (← getMCtx).mvarCounter
    let val ← k
    let newMVarIds ← getMVarsNoDelayed val
    /- ignore let-rec auxiliary variables, they are synthesized automatically later -/
    let newMVarIds ← newMVarIds.filterM fun mvarId => return !(← Term.isLetRecAuxMVar mvarId)
    /- Filter out all mvars that were created prior to `k`. -/
    let newMVarIds ← filterOldMVars newMVarIds mvarCounterSaved
    /- If `allowedHoles := .disallowNaturalHoles`, all natural mvarIds must be assigned.
    Passing this guard ensures that `newMVarIds` does not contain unassigned natural mvars. -/
    if allowedHoles = .disallowNaturalHoles then
      let naturalMVarIds ← newMVarIds.filterM fun mvarId => return (← mvarId.getKind).isNatural
      logUnassignedAndAbort naturalMVarIds
    /- We sort the new metavariable ids by index to ensure the new goals are ordered using the
    order the metavariables have been created. -/
    let newMVarIds ← sortMVarIdsByIndex newMVarIds.toList
    if let some tagSuffix := tagSuffix then tagUntaggedGoals (← getMainTag) tagSuffix newMVarIds
    return (val, newMVarIds)

/--
  Like `elabTermWithHoles`, elaborates `stx` and collects new `MVarId`s occurring in the result.
  It has three key differences:

  1. We may preserve the `MetavarKind` of metavariables with `allowedHoles := .allowNaturalHoles`.
  2. We do not tag untagged goals if `tagSuffix := none`.
  3. We may postpone metavariable assignments via `mayPostpone := true` (`mayPostpone := false` by
     default).

  Note that `allowedHoles` can take three values: `.disallowNaturalHoles` (which replicates
  `refine` behavior), `.allowNaturalHolesAsSyntheticOpaque` (which replicates `refine'` behavior),
  and `.allowNaturalHoles`, which preserves `MetavarKind`s as described in (1).
-/
def elabTermWithHoles' (stx : Syntax) (expectedType? : Option Expr)
    (tagSuffix : Option Name := none) (allowedHoles : AllowedHoles := .disallowNaturalHoles)
    (mayPostpone := false) : TacticM (Expr × List MVarId) :=
  withCollectingNewGoalsFrom'
    (elabTermEnsuringType stx expectedType? mayPostpone) tagSuffix allowedHoles

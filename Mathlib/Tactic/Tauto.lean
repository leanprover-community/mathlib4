/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, David Renshaw
-/
module

public import Mathlib.Logic.Basic  -- shake: keep (dependency of tactic output)
public meta import Qq
public meta import Mathlib.Lean.Meta
public import Mathlib.Tactic.CasesM
public import Mathlib.Tactic.Core

/-!
The `tauto` tactic.
-/
set_option backward.defeqAttrib.useBackward true

public meta section

namespace Mathlib.Tactic.Tauto

open Lean Elab.Tactic Parser.Tactic Lean.Meta MVarId Batteries.Tactic
open Qq

initialize registerTraceClass `tauto

/-- Tries to apply de-Morgan-like rules on a hypothesis. -/
def distribNotOnceAt (hypFVar : Expr) (g : MVarId) : MetaM AssertAfterResult := g.withContext do
  let .fvar fvarId := hypFVar | throwError "not fvar {hypFVar}"
  let h ← fvarId.getDecl
  let e : Q(Prop) ← (do guard <| ← Meta.isProp h.type; pure h.type)
  let replace (p : Expr) : MetaM AssertAfterResult := do
    commitIfNoEx do
      let result ← g.assertAfter fvarId h.userName (← inferType p) p
      /-
        We attempt to clear the old hypothesis. Doing so is crucial for
        avoiding infinite loops. On failure, we roll back the MetaM state
        and ignore this hypothesis. See
        https://github.com/leanprover-community/mathlib4/issues/10590.
      -/
      let newGoal ← result.mvarId.clear fvarId
      return { result with mvarId := newGoal }

  match e with
  | ~q(¬ ($a : Prop) = $b) => do
    let h' : Q(¬$a = $b) := h.toExpr
    replace q(mt propext $h')
  | ~q(($a : Prop) = $b) => do
    let h' : Q($a = $b) := h.toExpr
    replace q(Eq.to_iff $h')
  | ~q(¬ (($a : Prop) ∧ $b)) => do
    let h' : Q(¬($a ∧ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_and_iff_not_or_not'.mp $h')
  | ~q(¬ (($a : Prop) ∨ $b)) => do
    let h' : Q(¬($a ∨ $b)) := h.toExpr
    replace q(not_or.mp $h')
  | ~q(¬ (($a : Prop) ≠ $b)) => do
    let h' : Q(¬($a ≠ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable ($a = $b))
    replace q(Decidable.of_not_not $h')
  | ~q(¬¬ ($a : Prop)) => do
    let h' : Q(¬¬$a) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.of_not_not $h')
  | ~q(¬ ((($a : Prop)) → $b)) => do
    let h' : Q(¬($a → $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_imp_iff_and_not.mp $h')
  | ~q(¬ (($a : Prop) ↔ $b)) => do
    let h' : Q(¬($a ↔ $b)) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.not_iff.mp $h')
  | ~q(($a : Prop) ↔ $b) => do
    let h' : Q($a ↔ $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $b)
    replace q(Decidable.iff_iff_and_or_not_and_not.mp $h')
  | ~q((((($a : Prop)) → False) : Prop)) =>
    throwError "distribNot found nothing to work on with negation"
  | ~q((((($a : Prop)) → $b) : Prop)) => do
    let h' : Q($a → $b) := h.toExpr
    let _inst ← synthInstanceQ q(Decidable $a)
    replace q(Decidable.not_or_of_imp $h')
  | _ => throwError "distribNot found nothing to work on"

/--
State of the `distribNotAt` function. We need to carry around the list of
remaining hypothesis as fvars so that we can incrementally apply the
`AssertAfterResult.subst` from each step to each of them. Otherwise,
they could end up referring to old hypotheses.
-/
structure DistribNotState where
  /-- The list of hypothesis left to work on, renamed to be up-to-date with
  the current goal. -/
  fvars : List Expr

  /-- The current goal. -/
  currentGoal : MVarId

/--
Calls `distribNotAt` on the head of `state.fvars` up to `nIters` times, returning
early on failure.
-/
partial def distribNotAt (nIters : Nat) (state : DistribNotState) : MetaM DistribNotState :=
  match nIters, state.fvars with
  | 0, _ | _, [] => pure state
  | n + 1, fv::fvs => do
    try
      let result ← distribNotOnceAt fv state.currentGoal
      let newFVars := mkFVar result.fvarId :: fvs.map (fun x ↦ result.subst.apply x)
      distribNotAt n ⟨newFVars, result.mvarId⟩
    catch _ => pure state

/--
For each fvar in `fvars`, calls `distribNotAt` and carries along the resulting
renamings.
-/
partial def distribNotAux (fvars : List Expr) (g : MVarId) : MetaM MVarId :=
  match fvars with
  | [] => pure g
  | _ => do
    let result ← distribNotAt 3 ⟨fvars, g⟩
    distribNotAux result.fvars.tail! result.currentGoal

/--
Tries to apply de-Morgan-like rules on all hypotheses.
Always succeeds, regardless of whether any progress was actually made.
-/
def distribNot : TacticM Unit := withMainContext do
  let mut fvars := []
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      fvars := mkFVar h.fvarId :: fvars
  liftMetaTactic' (distribNotAux fvars)

/-- Config for the `tauto` tactic. Currently empty. TODO: add `closer` option. -/
structure Config

/-- Function elaborating `Config`. -/
declare_config_elab elabConfig Config

/-- Matches propositions where we want to apply the `constructor` tactic
in the core loop of `tauto`. -/
def coreConstructorMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(True) => pure true
  | _ => pure false

/-- Matches propositions where we want to apply the `cases` tactic
in the core loop of `tauto`. -/
def casesMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ∨ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(False) => pure true
  | _ => pure false

@[inherit_doc]
local infixl: 50 " <;> " => andThenOnSubgoals

/-- The core loop of the `tauto` tactic. Repeatedly tries to break down propositions
until no more progress can be made. Tries `assumption` and `contradiction` at every
step, to discharge goals as soon as possible. Does not do anything that requires
backtracking.

TODO: The Lean 3 version uses more-powerful versions of `contradiction` and `assumption`
that additionally apply `symm` and use a fancy union-find data structure to avoid
duplicated work.
-/
def tautoCore : TacticM Unit := do
  _ ← tryTactic (evalTactic (← `(tactic| contradiction)))
  _ ← tryTactic (evalTactic (← `(tactic| assumption)))
  iterateUntilFailure do
    let gs ← getUnsolvedGoals
    allGoals (
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      distribNot <;>
      liftMetaTactic (casesMatching casesMatcher (recursive := true) (throwOnNoMatch := false)) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · coreConstructorMatcher
        (recursive := true) (throwOnNoMatch := false)) <;>
      do _ ← tryTactic (evalTactic (← `(tactic| assumption))))
    let gs' ← getUnsolvedGoals
    if gs == gs' then failure -- no progress
    pure ()

/-- Matches propositions where we want to apply the `constructor` tactic in the
finishing stage of `tauto`. -/
def finishingConstructorMatcher (e : Q(Prop)) : MetaM Bool :=
  match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(True) => pure true
  | _ => pure false

/-- Implementation of the `tauto` tactic. -/
def tautology : TacticM Unit := focus do
  classical do
    let g ← getMainGoal
    tautoCore
    allGoals (iterateUntilFailure
      (evalTactic (← `(tactic| rfl)) <|>
      evalTactic (← `(tactic| solve_by_elim)) <|>
      liftMetaTactic (constructorMatching · finishingConstructorMatcher)))
    unless (← getUnsolvedGoals).isEmpty do
      throwTacticEx `tauto g

/--
`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `rfl` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.

The Lean 3 version of this tactic by default attempted to avoid classical reasoning
where possible. This Lean 4 version makes no such attempt. The `itauto` tactic
is designed for that purpose.
-/
syntax (name := tauto) "tauto" optConfig : tactic

elab_rules : tactic | `(tactic| tauto $cfg:optConfig) => do
  let _cfg ← elabConfig cfg
  tautology

end Mathlib.Tactic.Tauto

open Mathlib.TacticAnalysis

/-- Report places where `tauto` can be replaced by `grind`. -/
register_option linter.tacticAnalysis.tautoToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.tautoToGrind,
  inherit_doc linter.tacticAnalysis.tautoToGrind]
def tautoToGrind :=
  terminalReplacement "tauto" "grind" ``Mathlib.Tactic.Tauto.tauto (fun _ _ _ => `(tactic| grind))
    (reportSuccess := true) (reportFailure := false)

/-- Debug `grind` by identifying places where it does not yet supersede `tauto`. -/
register_option linter.tacticAnalysis.regressions.tautoToGrind : Bool := {
  defValue := false
}
@[tacticAnalysis linter.tacticAnalysis.regressions.tautoToGrind,
  inherit_doc linter.tacticAnalysis.regressions.tautoToGrind]
def tautoToGrindRegressions := grindReplacementWith "tauto" `Mathlib.Tactic.Tauto.tauto

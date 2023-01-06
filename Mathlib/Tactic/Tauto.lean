/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, David Renshaw
-/

import Lean
import Mathlib.Init.Logic
import Mathlib.Init.Propext
import Mathlib.Logic.Basic
import Mathlib.Tactic.CasesM
import Mathlib.Tactic.Classical
import Mathlib.Tactic.Core
import Mathlib.Tactic.SolveByElim
import Qq.Match

/-!
The `tauto` tactic.
-/

namespace Mathlib.Tactic.Tauto

open Lean Elab.Tactic Parser.Tactic Lean.Meta
open Qq

initialize registerTraceClass `tauto

/-- Tries to apply de-Morgan-like rules on a hypothesis. -/
def distribNotAt (h : LocalDecl) (g : MVarId) : MetaM MVarId := do
  let e : Q(Prop) ← (do guard (← inferType h.type).isProp; pure h.type)
  let replace (p : Expr) := g.replace h.fvarId p
  let result ← match e with
  | ~q(¬ ($a : Prop) = $b) => do
    let h' : Q(¬$a = $b) := h.toExpr
    replace q(mt Iff.to_eq $h')
  | ~q(($a : Prop) = $b) => do
    let h' : Q($a = $b) := h.toExpr
    replace q(Eq.to_iff $h')
  | ~q(¬ (($a : Prop) ∧ $b)) => do
    let h' : Q(¬($a ∧ $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
    replace q(Decidable.not_and'.mp $h')
  | ~q(¬ (($a : Prop) ∨ $b)) => do
    let h' : Q(¬($a ∨ $b)) := h.toExpr
    replace q(not_or.mp $h')
  | ~q(¬ (($a : Prop) ≠ $b)) => do
    let h' : Q(¬($a ≠ $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable ($a = $b)) : Q(Type))
    replace q(Decidable.of_not_not $h')
  | ~q(¬¬ ($a : Prop)) => do
    let h' : Q(¬¬$a) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
    replace q(Decidable.of_not_not $h')
  | ~q(¬ ((($a : Prop)) → $b)) => do
    let h' : Q(¬($a → $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
    replace q(Decidable.not_imp.mp $h')
  | ~q(¬ (($a : Prop) ↔ $b)) => do
    let h' : Q(¬($a ↔ $b)) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
    replace q(Decidable.not_iff.mp $h')
  | ~q(($a : Prop) ↔ $b) => do
    let h' : Q($a ↔ $b) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
    replace q(Decidable.iff_iff_and_or_not_and_not.mp $h')
  | ~q((((($a : Prop)) → False) : Prop)) =>
    throwError "distribNot found nothing to work on with negation"
  | ~q((((($a : Prop)) → $b) : Prop)) => do
    let h' : Q($a → $b) := h.toExpr
    let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
    replace q(Decidable.not_or_of_imp $h')
  | _ => throwError "distribNot found nothing to work on"
  pure result.mvarId

/--
Tries to apply de-Morgan-like rules on all hypotheses.
Always succeeds, regardless of whether any progress was actually made.
-/
def distribNot : TacticM Unit := withMainContext do
  for h in ← getLCtx do
    if !h.isImplementationDetail then
      iterateAtMost 3 $ liftMetaTactic' (distribNotAt h)

/-- Config for the `tauto` tactic. Currently empty. TODO: add `closer` option. -/
structure Config

/-- Function elaborating `Config`. -/
declare_config_elab elabConfig Config

/-- Matches propositions where we want to apply the `constructor` tactic
in the core loop of `tauto`. -/
def coreConstructorMatcher (e : Q(Prop)) : MetaM Bool := match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(True) => pure true
  | _ => pure false

/-- Matches propositions where we want to apply the `cases` tactic
in the core loop of `tauto`. -/
def casesMatcher (e : Q(Prop)) : MetaM Bool := match e with
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
      liftMetaTactic (casesMatching · casesMatcher) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (←`(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do pure [(← m.intros!).2]) <;>
      liftMetaTactic (constructorMatching · coreConstructorMatcher) <;>
      do _ ← tryTactic (evalTactic (← `(tactic| assumption))))
    let gs' ← getUnsolvedGoals
    if gs == gs' then failure -- no progress
    pure ()

/-- Matches propositions where we want to apply the `constructor` tactic in the
finishing stage of `tauto`. -/
def finishingConstructorMatcher (e : Q(Prop)) : MetaM Bool := match e with
  | ~q(_ ∧ _) => pure true
  | ~q(_ ↔ _) => pure true
  | ~q(Exists _) => pure true
  | ~q(True) => pure true
  | _ => pure false

/-- Implementation of the `tauto` tactic. -/
def tautology : TacticM Unit := focus do
  evalTactic (← `(tactic| classical!))
  tautoCore
  allGoals (iterateUntilFailure
    (evalTactic (← `(tactic| rfl)) <|>
     evalTactic (← `(tactic| solve_by_elim)) <|>
     liftMetaTactic (constructorMatching · finishingConstructorMatcher)))
  done

/--
`tauto` breaks down assumptions of the form `_ ∧ _`, `_ ∨ _`, `_ ↔ _` and `∃ _, _`
and splits a goal of the form `_ ∧ _`, `_ ↔ _` or `∃ _, _` until it can be discharged
using `reflexivity` or `solve_by_elim`.
This is a finishing tactic: it either closes the goal or raises an error.

The Lean 3 version of this tactic by default attempted to avoid classical reasoning
where possible. This Lean 4 version makes no such attempt. The `itauto` tactic
is designed for that purpose.
-/
syntax (name := tauto) "tauto" (config)? : tactic

elab_rules : tactic | `(tactic| tauto $[$cfg:config]?) => do
  let _cfg ← elabConfig (mkOptionalNode cfg)
  tautology

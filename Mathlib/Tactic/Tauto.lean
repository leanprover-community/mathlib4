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

/-- Like `replace`, but infers the type of the proof. -/
private def replace' (g : MVarId) (hyp : FVarId) (proof : Expr) :
    MetaM AssertAfterResult :=
  do let t ← inferType proof
     g.replace hyp t proof

/-- Repeats a tactic at most `n` times, stopping sooner if the
tactic fails. Always returns success. -/
private def iterateAtMost : Nat → TacticM Unit → TacticM Unit
| 0, _ => pure ()
| n + 1, tac => do
      if ← tryTactic tac
      then iterateAtMost n tac
      else pure ()

/-- Repeats a tactic until it fails. Always returns success. -/
partial def iterateUntilFailure (tac : TacticM Unit) : TacticM Unit :=
  try do tac; iterateUntilFailure tac
  catch _ => pure ()

/-- Tries to apply de-Morgan-like rules on all hypotheses. Always succeeds,
regardless of whether any progress was actually made.
-/
def distribNot : TacticM Unit := withMainContext do
for h in ← getLCtx do
 iterateAtMost 3 $
  liftMetaTactic fun mvarId =>  do
    let e : Q(Prop) ← (do let htt ← inferType h.type
                          guard htt.isProp
                          pure h.type)
    match e with
    | ~q(¬ ($a : Prop) = $b) => do
      let h' : Q(¬$a = $b) := mkFVar h.fvarId
      let result ← replace' mvarId h.fvarId (q(mt Iff.to_eq $h'))
      pure [result.mvarId]
    | ~q(($a : Prop) = $b) => do
      let h' : Q($a = $b) := mkFVar h.fvarId
      let result ← replace' mvarId h.fvarId (q(Eq.to_iff $h'))
      pure [result.mvarId]
    | ~q(¬ (($a : Prop) ∧ $b)) => do
      let h' : Q(¬($a ∧ $b)) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.not_and'.mp $h'))
      pure [result.mvarId]
    | ~q(¬ (($a : Prop) ∨ $b)) => do
      let h' : Q(¬($a ∨ $b)) := mkFVar h.fvarId
      let result ← replace' mvarId h.fvarId (q(not_or.mp $h'))
      pure [result.mvarId]
    | ~q(¬ (($a : Prop) ≠ $b)) => do
      let h' : Q(¬($a ≠ $b)) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable ($a = $b)) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.of_not_not $h'))
      pure [result.mvarId]
    | ~q(¬¬ ($a : Prop)) => do
      let h' : Q(¬¬$a) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.of_not_not $h'))
      pure [result.mvarId]
    | ~q(¬ ((($a : Prop)) → $b)) => do
      let h' : Q(¬($a → $b)) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.not_imp.mp $h'))
      pure [result.mvarId]
    | ~q(¬ (($a : Prop) ↔ $b)) => do
      let h' : Q(¬($a ↔ $b)) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.not_iff.mp $h'))
      pure [result.mvarId]
    | ~q(($a : Prop) ↔ $b) => do
      let h' : Q($a ↔ $b) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable $b) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.iff_iff_and_or_not_and_not.mp $h'))
      pure [result.mvarId]
    | ~q((((($a : Prop)) → False) : Prop)) =>
      throwError "distribNot found nothing to work on with negation"
    | ~q((((($a : Prop)) → $b) : Prop)) => do
      let h' : Q($a → $b) := mkFVar h.fvarId
      let _inst ← synthInstanceQ (q(Decidable $a) : Q(Type))
      let result ← replace' mvarId h.fvarId (q(Decidable.not_or_of_imp $h'))
      pure [result.mvarId]
    | _ => throwError "distribNot found nothing to work on"

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

/-- Applies `intro` repeatedly until it fails. We use this instead of plain
`MVarId.intros` because we want it to propositions like `¬p`. The `¬` needs
to be unfolded into `→ False`, and `intros` does not do such unfolding. -/
partial def intros' (mvarId : MVarId) : MetaM MVarId :=
  try
    let ⟨_, m1⟩ ← mvarId.intro1
    intros' m1
  catch _ =>
    pure mvarId

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
      liftMetaTactic (fun m => do let m' ← intros' m; pure [m']) <;>
      distribNot <;>
      liftMetaTactic (casesMatching · casesMatcher) <;>
      (do _ ← tryTactic (evalTactic (← `(tactic| contradiction)))) <;>
      (do _ ← tryTactic (evalTactic (←`(tactic| refine or_iff_not_imp_left.mpr ?_)))) <;>
      liftMetaTactic (fun m => do let m' ← intros' m; pure [m']) <;>
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

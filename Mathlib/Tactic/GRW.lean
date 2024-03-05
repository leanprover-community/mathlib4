/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer, Mario Carneiro, Heather Macbeth
-/
import Mathlib.Tactic.GRW.Lemmas

/-!
# `grw` tactic

A generalization of the `rw` tactic to work with relations other than equality.

-/

namespace Mathlib.Tactic

open Lean Meta Elab Parser Tactic Mathlib.Tactic.GRW

/-- Apply the rewrite rule `rule` at hypothesis `fvar`.
If `rev` is true, rewrite from right to left instead of left to right. -/
def grwAtLocal (rev : Bool) (rule : Term) (fvar : FVarId) : TacticM Unit := do
  let goal ← getMainGoal
  Term.withSynthesize <| goal.withContext do
    let rulePrf ← elabTerm rule none true
    let (newType, implication, newSubgoals) ← goal.grw (← fvar.getType) rulePrf rev false
    let name ← fvar.getUserName
    let ⟨_, goal', _⟩ ← goal.assertAfter fvar name newType <| .betaRev implication #[.fvar fvar]
    let newGoal ← goal'.clear fvar
    replaceMainGoal (newGoal :: newSubgoals.toList)

/-- Apply the rewrite rule `rule` at the goal.
If `rev` is true, rewrite from right to left instead of left to right. -/
def grwAtTarget (rev : Bool) (rule : Term) : TacticM Unit := do
  let goal ← getMainGoal
  Term.withSynthesize <| goal.withContext do
    let rulePrf ← elabTerm rule none true
    let (newType, implication, newSubgoals) ← goal.grw (← goal.getType) rulePrf rev true
    let newGoal ← mkFreshExprSyntheticOpaqueMVar newType (← goal.getTag)
    goal.assign <| .betaRev implication #[newGoal]
    replaceMainGoal (newGoal.mvarId! :: newSubgoals.toList)

/--
`grw` is a generalization of the `rw` tactic that takes other relations than equality.  For example,
```lean
example (h₁ : a + e ≤ b + e)
    (h₂ : b < c)
    (h₃ : c ≤ d) :
    a + e ≤ d + e := by
  grw [h₂, h₃] at h₁
  exact h₁
```

If applied to a hypothesis or target of type `p` with rule of type `x ~ y` (where `~` is some
relation) then the resulting type will be `p[x/y]`.

If applied to the target then the tactic will attempt to close the goal with `rfl` after doing the
rewriting.
-/
elab tok:"grw" rules:rwRuleSeq loc:(location)? : tactic => do
  withRWRulesSeq tok rules fun rev stx ↦ do
    withLocation (expandOptLocation (Lean.mkOptionalNode loc))
      (atLocal := grwAtLocal rev ⟨stx⟩)
      (atTarget := grwAtTarget rev ⟨stx⟩)
      (failed := fun _ ↦ throwError "grw failed")
  let goal ← getMainGoal
  try goal.withContext <| Meta.withReducible goal.applyRfl
  catch _ => pure ()

/-
Copyright (c) 2023 Sebastian Zimmer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Zimmer
-/
import Mathlib.Lean.Meta
import Mathlib.Lean.Expr
import Mathlib.Lean.Elab.Tactic.Basic
import Lean.Parser.Tactic
import Lean.Meta.Tactic
import Mathlib.Tactic.GRW.Core
import Mathlib.Tactic.GRW.Lemmas

/-!
# `grw` tactic

A generalization of the `rw` tactic to work with relations other than equality.

-/

namespace Mathlib.Tactic

open Lean Meta Elab Parser Tactic Mathlib.Tactic.GRW

-- TODO these should probably be public with a nicer API?
private partial def grwHypothesis (hyp : Expr) (rule : Expr) (rev : Bool) :
    MetaM (Expr × Expr × Array MVarId) := do
  let ⟨newType, newHyp, _, subgoals⟩ ← runGrw hyp rule rev false
  return ⟨newType, newHyp, subgoals⟩

private partial def _root_.Lean.MVarId.grw (goal : MVarId) (rule : Expr) (rev : Bool := false) :
    MetaM (MVarId × Array MVarId) := do
  let ⟨_, prf, mvar, subgoals⟩ ← runGrw (Expr.mvar goal) rule rev true
  goal.assign prf
  return ⟨mvar, subgoals⟩

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
relation) then the resulting type will be `p[x/y]` or the tactic will fail. This tactic will fail
if side goals are created that it can not fill itself, which it does using `positivity` or
`assumption`. These two facts make it safe to use in a nonterminal position.
-/
elab tok:"grw" rules:rwRuleSeq loc:(location)? : tactic =>
  withMainContext do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := λ fvar => do
      -- TODO this is a horrible hack, maybe just don't use withRWRulesSeq?
      -- we use an mvar to keep track of which fvar we are up to (since we replace the fvar after
      -- applying each rule )

      let mvar := (← mkFreshExprMVar none).mvarId!
      mvar.assign (Expr.fvar fvar)

      withRWRulesSeq tok rules fun rev syn ↦ withMainContext do
        let fvar ← if let some fvarExpr := ← (Lean.getExprMVarAssignment? mvar) then
          pure fvarExpr.fvarId!
        else
          throwError "Lost track of fvar"
        let rulePrf ← elabTerm syn none
        let ⟨newType, newHyp, subgoals⟩ ← grwHypothesis (Expr.fvar fvar) rulePrf rev
        let name ← fvar.getUserName
        let ⟨newFvar, newGoal, _⟩ ← (← getMainGoal).assertAfter fvar name newType newHyp
        replaceMainGoal (subgoals.push (← newGoal.clear fvar)).toList
        mvar.assign (Expr.fvar newFvar)
    )
    (atTarget := withRWRulesSeq tok rules fun rev syn ↦ withMainContext do
      let rulePrf ← elabTerm syn none
      let ⟨newGoal, subgoals⟩ ← (← getMainGoal).grw rulePrf rev
      try
        withReducible newGoal.applyRfl
        trace[GRW] "Solve main goal with `rfl`"
        replaceMainGoal subgoals.toList
      catch _ =>
        replaceMainGoal (subgoals.push newGoal).toList
    )
    (failed := fun _ ↦ throwError "grw failed")

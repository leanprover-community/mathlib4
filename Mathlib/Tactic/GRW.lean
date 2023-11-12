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
import Std.Tactic.LabelAttr
import Mathlib.Tactic.GRW.Core
import Mathlib.Tactic.GRW.Lemmas

namespace Mathlib.Tactic

open Lean Meta Elab Parser Tactic Mathlib.Tactic.GRW

private partial def grwHypothesis (hyp : Expr) (rule : Expr) (rev : Bool) : MetaM (Expr × Expr) := do
  let ⟨newType, newHyp, _⟩ ← runGrw hyp rule rev false
  return ⟨newType, newHyp⟩

partial def _root_.Lean.MVarId.grw (goal : MVarId) (rule : Expr) (rev : Bool := false)
    : MetaM MVarId := do
  let ⟨_, prf, mvar⟩ ← runGrw (Expr.mvar goal) rule rev true
  goal.assign prf
  return mvar

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
        let ⟨newType, newHyp⟩ ← grwHypothesis (Expr.fvar fvar) rulePrf rev

        let ⟨newFvar, newGoal, _⟩ ← (← getMainGoal).assertAfter fvar (← fvar.getUserName) newType newHyp
        replaceMainGoal [← newGoal.clear fvar]
        mvar.assign (Expr.fvar newFvar)
    )
    (atTarget := withRWRulesSeq tok rules fun rev syn ↦ withMainContext do
      let rulePrf ← elabTerm syn none
      let newGoal ← (← getMainGoal).grw rulePrf rev
      replaceMainGoal [newGoal]
    )
    (failed := fun ex ↦ throwError "grw failed")

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
  let ⟨_, _, mvar, subgoals⟩ ← runGrw (Expr.mvar goal) rule rev true
  return ⟨mvar, subgoals⟩

/-- A version of `withRWRulesSeq` (in core) that doesn't attempt to find equation lemmas, and
allows the caller to maintain state via StateT. -/
private partial def withRWRulesSeqState {State : Type} (token : Syntax) (rwRulesSeqStx : Syntax)
    (x : (symm : Bool) → (term : Syntax) → StateT State TacticM Unit) :
    StateT State TacticM Unit := do
  let lbrak := rwRulesSeqStx[0]
  let rules := rwRulesSeqStx[1].getArgs
  -- show initial state up to (incl.) `[`
  withTacticInfoContext (mkNullNode #[token, lbrak]) (pure ())
  let numRules := (rules.size + 1) / 2
  for i in [:numRules] do
    let rule := rules[i * 2]!
    let sep  := rules.getD (i * 2 + 1) Syntax.missing
    let state ← get
    -- show rule state up to (incl.) next `,`
    let newState ← withTacticInfoContext (mkNullNode #[rule, sep]) do
      -- show errors on rule
      let s ← withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        let ⟨_, newState⟩ ← (x symm term).run state
        return newState
      return s
    set newState

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
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := λ fvar => withMainContext do
      let ⟨_, newGoal, subgoals, _⟩ ← (withRWRulesSeqState tok rules fun rev syn ↦ do
        let ⟨goal, subgoals, fvar⟩ ← get
        goal.withContext do
          let rulePrf ← elabTerm syn none
          let ⟨newType, newHyp, newSubgoals⟩ ← goal.withContext
              $ grwHypothesis (Expr.fvar fvar) rulePrf rev
          let name ← fvar.getUserName
          let ⟨newFvar, goal', _⟩ ← goal.assertAfter fvar name newType newHyp
          let newGoal ← goal'.clear fvar
          set (⟨newGoal, subgoals ++ newSubgoals, newFvar⟩ : MVarId × Array MVarId × FVarId)
      ).run (⟨← getMainGoal, #[], fvar⟩ : MVarId × Array MVarId × FVarId)
      -- We can't use replaceMainGoal, since withTacticInfoContext prunes the solved goals so the
      -- main goal will have already been removed
      let newGoals := subgoals ++ #[newGoal] ++ (← getGoals)
      setGoals newGoals.toList
      pruneSolvedGoals
    )
    (atTarget := withMainContext do
      let ⟨_, newGoal, subgoals⟩ ← (withRWRulesSeqState tok rules fun rev syn ↦ do
        let ⟨currentTarget, subgoals⟩ ← get
        let ⟨newGoal, newSubgoals⟩ ← currentTarget.withContext do
          let rulePrf ← elabTerm syn none
          currentTarget.grw rulePrf rev
        set (⟨newGoal, subgoals.append newSubgoals⟩ : MVarId × Array MVarId)
      ).run (⟨← getMainGoal, #[]⟩ : MVarId × Array MVarId)
      try newGoal.withContext $ withReducible newGoal.applyRfl
      catch _ => pure ⟨⟩
      -- We can't use replaceMainGoal, since withTacticInfoContext prunes the solved goals so the
      -- main goal will have already been removed
      let newGoals := subgoals.toList ++ [newGoal] ++ (← getGoals)
      setGoals newGoals
      pruneSolvedGoals
    )
    (failed := fun _ ↦ throwError "grw failed")

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
      withRef rule do
        let symm := !rule[0].isNone
        let term := rule[1]
        -- let processId (id : Syntax) : TacticM Unit := do
        let ⟨_, newState⟩ ← (x symm term).run state
        return newState
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
relation) then the resulting type will be `p[x/y]` or the tactic will fail. This tactic will fail
if side goals are created that it can not fill itself, which it does using `positivity` or
`assumption`. These two facts make it safe to use in a nonterminal position.
-/
elab tok:"grw" rules:rwRuleSeq loc:(location)? : tactic => do
  withLocation (expandOptLocation (Lean.mkOptionalNode loc))
    (atLocal := λ fvar => withMainContext do
      let _ ← (withRWRulesSeqState tok rules fun rev syn ↦ do
        let fvar ← get
        let rulePrf ← elabTerm syn none
        let ⟨newType, newHyp, subgoals⟩ ← grwHypothesis (Expr.fvar fvar) rulePrf rev
        let name ← fvar.getUserName
        let ⟨newFvar, newGoal, _⟩ ← (← getMainGoal).assertAfter fvar name newType newHyp
        replaceMainGoal (subgoals.push (← newGoal.clear fvar)).toList
        set newFvar
      ).run fvar
    )
    (atTarget := withMainContext do
      let ⟨_, newGoal, subgoals⟩ ← (withRWRulesSeqState tok rules fun rev syn ↦ do
        let ⟨currentTarget, subgoals⟩ ← get
        trace[GRW] "Processing step {currentTarget} {subgoals}"
        let ⟨newGoal, newSubgoals⟩ ← currentTarget.withContext do
          let rulePrf ← elabTerm syn none
          currentTarget.grw rulePrf rev
        trace[GRW] "Finished step {newGoal} {subgoals.append newSubgoals}"
        set (⟨newGoal, subgoals.append newSubgoals⟩ : MVarId × Array MVarId)
      ).run (⟨← getMainGoal, #[]⟩ : MVarId × Array MVarId)
      -- try
      --   trace[GRW] "Trying to solve main goal with rfl"
      --   newGoal.withContext $ withReducible newGoal.applyRfl
      --   trace[GRW] "Solve main goal with `rfl`"
      --   replaceMainGoal subgoals.toList
      -- catch _ =>
      trace[GRW] "Could not solve main goal with rfl"
      trace[GRW] "Replacing main goals with {subgoals.push newGoal} {← newGoal.isAssigned}"
      replaceMainGoal (subgoals.push newGoal).toList
    )
    (failed := fun _ ↦ throwError "grw failed")

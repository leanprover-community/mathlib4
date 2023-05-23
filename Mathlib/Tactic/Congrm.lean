/-
Copyright (c) 2023 Moritz Doll, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Gabriel Ebner, Damiano Testa
-/

import Mathlib.Tactic.Basic
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic -- only needed for tests


namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

syntax (name := congrM) "congrm " term : tactic

#check forallTelescope
#check elabTermEnsuringType
#check liftMetaTactic
#check MVarId.apply

private def applyCongrThm? (mvarId : MVarId) (congrThm : CongrTheorem) : MetaM (List MVarId) := do
  let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThm.type congrThm.proof
  let (fvarId, mvarId) ← mvarId.intro1P
  let mvarIds ← mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
  mvarIds.mapM fun mvarId => mvarId.tryClear fvarId

partial def congrm_core (pat : Expr) : TacticM Unit := withMainContext do
  -- Helper function (stolen from somewhere) that creates the correct FVars in `λ` and `∀`
  -- and does the recursion
  let binders (stx : Syntax) (xs : Array Expr) (k : Expr) : TacticM Unit := do
    for x in xs do
      let localDecl ← x.fvarId!.getDecl
      evalTactic stx
      liftMetaTactic fun mvarId => do
        pure [(← mvarId.intro localDecl.userName).2]
    congrm_core k
  dbg_trace s!"Pattern {← ppExpr pat}"
  if pat.isForall then
    dbg_trace s!"Forall pattern"
    forallTelescope pat (binders (← `(tactic| apply pi_congr)))
  else if pat.isLambda then
    dbg_trace s!"Lambda pattern"
    lambdaTelescope pat (binders (← `(tactic| apply funext)))
  else if pat.isApp then
    let some congrThm ← mkCongrSimp? pat.getAppFn (subsingletonInstImplicitRhs := false) | return
    if congrThm.type.isMVar then
      dbg_trace s!"Invalid congr lemma"
      return

    if pat.getAppFn.isMVar then
      dbg_trace s!"Fun is metavar"
      return
    -- Should check whether the congr_lem is valid

    let foo ← applyCongrThm? (← getMainGoal) congrThm
    -- We should not set the goals, but see from which part each goal came and recursively apply
    -- patterns

    -- I think we can assume that #goals = #arguments
    setGoals foo

    dbg_trace s!"Apply pattern, fun: {← ppExpr pat.getAppFn}"
  --return
  /-match pat with
  | .forallE _name _type _body _info =>
    dbg_trace s!"Forall pattern"
    --return
    forallTelescope pat (binders (← `(tactic| apply pi_congr)))
  | .lam _name _type _body _info =>
    dbg_trace s!"Lambda pattern"
    --return
    lambdaTelescope pat (binders (← `(tactic| apply funext)))
  | .app fn arg =>
    --let congr_lem ← mkHCongr pat
    let some congrThm ← mkCongrSimp? pat.getAppFn (subsingletonInstImplicitRhs := false) | return
    if congrThm.type.isMVar then
      dbg_trace s!"Invalid congr lemma"
      return

    if fn.isMVar then
      dbg_trace s!"Fun is metavar"
      return
    -- Should check whether the congr_lem is valid

    let foo ← applyCongrThm? (← getMainGoal) congrThm
    setGoals foo
    dbg_trace s!"Apply pattern, fun: {← ppExpr fn}, arg: {← ppExpr arg }"
    -- Todo: We want to make sure that `fn` is the correct function name
    --evalTactic (← `(tactic| apply congr_arg))
    --congrm_core fn
    --let fn' ← whnf fn
    --evalTactic (← `(tactic| apply congr_arg))
    -- Need to get LHS and RHS of application in the goal
    /-liftMetaTactic fun mvarId => do
      let list ← mvarId.apply (← mkAppOptM ``congrArg #[none, none, none, none, some fn, none])
      return list-/
    --congrm_core arg -- Recursion on argument
    --congrm_core fn -- Recursion on function
  | _ =>-/
  --return


elab_rules : tactic | `(tactic| congrm $expr:term) => withMainContext do
  evalTactic (← `(tactic| try apply Eq.to_iff))
  let e ← elabTerm expr none
  congrm_core e


-- Fancy new tests

-- Testing that the trivial `forall` rule works:
example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ b : α, True) := by
  congrm (∀ x, _)
  exact h x

example (f : α → α → Prop) (h : ∀ a b, f a b = True) :
    (∀ a b, f a b) ↔ (∀ a b : α, True) := by
  congrm (∀ x y, _)
  exact h x y

-- Testing that the trivial `lambda` rule works:
example {a b : ℕ} (h : a = b) : (fun y : ℕ => y + a) = (fun x => x + b) := by
  congrm λ x => _
  rw [h]

-- Testing that trivial application rule works
example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f a = f b := by
  congrm (f _)
  exact h

-- Testing that application rule with two arguments works
example (a b c d : ℕ) (h : a = b) (h' : c = d) (f : ℕ → ℕ → ℕ) : f a c = f b d := by
  congrm (f _) -- this is slightly stupid
  exact h
  exact h'

-- Testing that application rule with recursion works
example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f (f a) = f (f b) := by
  congrm (f (f _))
  exact h

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (_ = _)
  rfl -- Todo: this should not be here
  exact h

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, (_ + a = w)
  simp only [h]
  rfl

#exit

-- Old bad tests

example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (a = _)
  exact h

example (f : α → Prop): (∀ a : α, f a) ↔ (∀ b : α, True) := by
  congrm (∀ x, _)

  --apply Eq.to_iff
  have : ∀ a, f a = True := sorry
  exact this x

example (f : α → α → Prop): (∀ a b, f a b) ↔ (∀ a b : α, True) := by
  congrm (∀ x y, _)
  have : ∀ a b, f a b = True := sorry
  exact this x y

example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f a = f b := by
  congrm (f _)
  exact h

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, (_ + a = w)
  --apply propext
  congr 1
  simp only [h]

example : (3 : ℤ) ≤ (3 : ℕ) := by
  simp only

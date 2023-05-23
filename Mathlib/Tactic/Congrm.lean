/-
Copyright (c) 2023 Moritz Doll, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Gabriel Ebner, Damiano Testa
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Congr!
import Mathlib.Logic.Basic
import Mathlib.Data.Nat.Basic -- only needed for tests


namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `trace.congrm

syntax (name := congrM) "congrm " term : tactic

/-- Given a function, extract the explicit arguments. -/
def _root_.Lean.Expr.getExplicitArgs (f : Expr) : MetaM (Array Expr) := do
  let args := f.getAppArgs
  let pinfo := (← Lean.Meta.getFunInfoNArgs f.getAppFn args.toList.length).paramInfo
  logInfo s!"all arguments: {← args.mapM ppExpr} and patternInfos: {pinfo.toList.length}"
  return (pinfo.zip args).filterMap (λ arg => if arg.1.isExplicit then some arg.2 else none)

def try_refl (goal : MVarId) : MetaM (Option MVarId) := do
  let res ← observing? do
    goal.refl
  if res == none then return some goal else return none

private def applyCongrThm? (mvarId : MVarId) (congrThm : CongrTheorem) : MetaM (List MVarId) := do
  let mvarId ← mvarId.assert (← mkFreshUserName `h_congr_thm) congrThm.type congrThm.proof
  let (fvarId, mvarId) ← mvarId.intro1P
  let mvarIds ← mvarId.apply (mkFVar fvarId) { synthAssignedInstances := false }
  mvarIds.mapM fun mvarId => mvarId.tryClear fvarId

partial def foo (lem : Name) (goal : MVarId) (x : Expr) : MetaM MVarId := do
  let localDecl ← x.fvarId!.getDecl
  let newGoals ← goal.apply (← mkConstWithFreshMVarLevels lem)
  if newGoals.length == 1 then
    let newGoal := newGoals[0]!
    return (← newGoal.intro localDecl.userName).2
  return goal

partial def congrm_loop (goal : MVarId) (pat : Expr) : MetaM (List MVarId) := do
  -- Helper function (stolen from somewhere) that creates the correct FVars in `λ` and `∀`
  -- and does the recursion
  let binders (mvarId : MVarId) (lem : Name) (xs : Array Expr) (k : Expr) : MetaM (List MVarId) := do
    congrm_loop (← xs.foldlM (foo lem) mvarId) k
  logInfo "Pattern {← ppExpr pat}"
  if pat.isForall then
    logInfo "Forall pattern"
    forallTelescope pat (binders goal ``pi_congr)
  else if pat.isLambda then
    logInfo "Lambda pattern"
    lambdaTelescope pat (binders goal ``funext)
  else if pat.isApp then
    let args := (← pat.getExplicitArgs).toList
    let some congrThm ← mkCongrSimp? pat.getAppFn' (subsingletonInstImplicitRhs := false) | return []
    if congrThm.type.isMVar then
      logInfo "Invalid congr lemma"
      return [goal]

    if pat.getAppFn.isMVar then
      logInfo "Fun is metavar"
      return [goal]
    -- Should check whether the congr_lem is valid

    let argumentList ← applyCongrThm? goal congrThm
    logInfo s!"Apply pattern, fun: {← ppExpr pat.getAppFn}"
    -- If the pattern has a different number of arguments, then we just fail:
    if argumentList.length != args.length then
      logInfo s!"Number of patterns and arguments are different:
        args: {argumentList.map MVarId.name}
        pat: {← pat.getAppArgs.mapM ppExpr}
         {← args.mapM ppExpr}"
      throwTacticEx `congrm goal m!"Number of function arguments does not match"
      --failure
      -- There is some problem with `Eq` `_ = _` has 2 arguments, but there appears only one argument
    -- We should not set the goals, but see from which part each goal came and recursively apply
    -- patterns

    let blubb := argumentList.zip args
    return (← blubb.mapM (λ (m,e) => congrm_loop m e)).join
  else return [goal]

partial def congrm_core_rly (goal : MVarId) (pat : Expr) : MetaM (List MVarId) := do
  -- First change `iff` to `=` and then run the loop:
  let mvars ← congrm_loop (← goal.iffOfEq) pat
  mvars.filterMapM try_refl

elab_rules : tactic | `(tactic| congrm $expr:term) => withMainContext do
  setGoals (← congrm_core_rly (← getMainGoal) (← elabTerm expr none))

syntax (name := prettyExpr) "prettyExpr " term : tactic

--elab_rules : tactic | `(tactic| prettyExpr $expr:term) => withMainContext do


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
  congrm (f _ _)
  exact h
  exact h'

-- Testing that application rule with recursion works
example (a b : ℕ) (h : a = b) (f : ℕ → ℕ) : f (f a) = f (f b) := by
  congrm (f (f _))
  exact h

-- Testing for implicit arguments in function application
example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (_ = _)
  exact h

-- Testing for implicit arguments in function application
example {α : Type} {f : α → α} (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (@Eq _ _ _)
  exact h

example {a b : ℕ} (h : a = b) : (fun y : ℕ => ∀ z, a + a = z) = (fun x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, (_ + a = w)
  simp only [h]

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

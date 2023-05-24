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

section util

/-- Given a function, extract the explicit arguments. -/
def _root_.Lean.Expr.getExplicitArgs (f : Expr) : MetaM (Array Expr) := do
  let args := f.getAppArgs
  let pinfo := (← Lean.Meta.getFunInfo f.getAppFn').paramInfo
  logInfo s!"all arguments: {← args.mapM ppExpr} and patternInfos: {pinfo.toList.length}"
  return (pinfo.zip args).filterMap (λ arg => if arg.1.isExplicit then some arg.2 else none)

def try_refl (goal : MVarId) : MetaM (Option MVarId) := do
  let res ← observing? do
    goal.refl
  if res == none then return some goal else return none

def _root_.Lean.MVarId.applyWithFreshMVarLevels (goal : MVarId) (lem : Name) :
    MetaM (List MVarId) := do
  goal.apply (← mkConstWithFreshMVarLevels lem)

def modifyMainGoal (f : MVarId → MetaM (List MVarId)) : TacticM Unit := withMainContext do
  setGoals <| ← f <| ← getMainGoal

end util

private partial def telescopingFn (lem : Name) (goal : MVarId) (x : Expr) : MetaM MVarId := do
  let userName ← x.fvarId!.getUserName
  let newGoals ← goal.applyWithFreshMVarLevels lem
  if newGoals.length == 1 then
    let newGoal := newGoals[0]!
    return (← newGoal.intro userName).2
  failure

open private applyCongrThm? from Lean.Meta.Tactic.Congr in

partial def congrm_loop (pat : Expr) (goal : MVarId) : MetaM (List MVarId) := goal.withContext do
  -- Helper function (stolen from somewhere) that creates the correct FVars in `λ` and `∀`
  -- and does the recursion
  let binders (mvarId : MVarId) (lem : Name) (xs : Array Expr) (k : Expr) : MetaM (List MVarId) := do
    congrm_loop k (← xs.foldlM (telescopingFn lem) mvarId)
  logInfo "Pattern {← ppExpr pat}"
  if pat.isMVar then
    return [goal]
  else if pat.isForall then
    logInfo "Forall pattern"
    forallTelescope pat (binders goal ``pi_congr)
  else if pat.isLambda then
    logInfo "Lambda pattern"
    lambdaTelescope pat (binders goal ``funext)
  else if pat.isApp then
    let patternArgs := (← pat.getExplicitArgs).toList
    let some congrThm ← mkCongrSimp? pat.getAppFn' (subsingletonInstImplicitRhs := false) | return []
    if pat.getAppFn.isMVar then
      logInfo "Fun is metavar"
      return [goal]

    let goalArgs ← applyCongrThm? goal congrThm
    logInfo s!"Apply pattern, fun: {← ppExpr pat.getAppFn}"
    -- If the pattern has a different number of arguments, then we just fail:
    if goalArgs.length != patternArgs.length then
      logInfo s!"Number of patterns and arguments are different:
        args: {goalArgs.map MVarId.name}
        pat: {← pat.getAppArgs.mapM ppExpr}
         {← patternArgs.mapM ppExpr}"
      throwTacticEx `congrm goal m!"Number of function arguments does not match"

    -- Apply `congrm_loop` to all arguments with the corresponding pattern and concat the resulting
    -- list.
    return (← (patternArgs.zip goalArgs).mapM (λ (e,m) => congrm_loop e m)).join
  else
    return [goal]
    --throwTacticEx `congrm goal m!"Invalid pattern"

partial def congrm_core (pat : Expr) (goal : MVarId) : MetaM (List MVarId) := do
  -- First change `iff` to `=` and then run the loop:
  let mvars ← congrm_loop pat (← goal.iffOfEq)
  mvars.filterMapM try_refl

elab_rules : tactic | `(tactic| congrm $expr:term) => withMainContext do
  modifyMainGoal <| congrm_core <| ← elabTerm expr none

-- Testing that the trivial `forall` rule works:
example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm (∀ x, _)
  exact h x

example (f : α → α → Prop) (h : ∀ a b, f a b = True) :
    (∀ a b, f a b) ↔ (∀ _ _ : α, True) := by
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

example {a b : ℕ} (h : a = b) : (fun _ : ℕ => ∀ z, a + a = z) = (fun _ => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, (_ + a = w)
  simp only [h]

-- Tests that should fail:


-- Testing for too many arguments
example (a b c : ℕ) (h : b = c) : a = b ↔ a = c := by
  congrm (Eq _ _ _) -- Todo: good error message
  exact h

-- Testing for wrong pattern
example (f : α → Prop) (h : ∀ a, f a = True) : (∀ a : α, f a) ↔ (∀ _ : α, True) := by
  congrm (f _)
  exact h x

/-
Copyright (c) 2023 Moritz Doll, Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll, Gabriel Ebner, Damiano Testa
-/

import Mathlib.Tactic.Basic
import Mathlib.Tactic.Congr!
import Mathlib.Logic.Basic

/-!
# The `congrm` tactic

to be written
 -/

namespace Mathlib.Tactic
open Lean Parser Tactic Elab Tactic Meta

initialize registerTraceClass `congrm

/--
Assume that the goal is of the form `lhs = rhs` or `lhs ↔ rhs`.
`congrm e` takes an expression `e` containing placeholders `_` and scans `e, lhs, rhs` in parallel.

It matches both `lhs` and `rhs` to the pattern `e`, and produces one goal for each placeholder,
stating that the corresponding subexpressions in `lhs` and `rhs` are equal.

Examples:
```lean
example {a b c d : ℕ} :
  Nat.pred a.succ * (d + (c + a.pred)) = Nat.pred b.succ * (b + (c + d.pred)) := by
  congrm Nat.pred (Nat.succ _) * (_ + _)
/-  Goals left:
⊢ a = b
⊢ d = b
⊢ c + a.pred = c + d.pred
-/
  sorry
  sorry
  sorry

example {a b : ℕ} (h : a = b) : (λ y : ℕ => ∀ z, a + a = z) = (λ x => ∀ z, b + a = z) := by
  congrm λ x => ∀ w, _ + a = w
  -- produces one goal for the underscore: ⊢ a = b
  exact h
```
-/
syntax (name := congrM) "congrm " term : tactic

section util

/-- Given a function, extract the explicit arguments. -/
def _root_.Lean.Expr.getExplicitArgs (f : Expr) : MetaM (Array Expr) := do
  let args := f.getAppArgs
  let pinfo := (← Lean.Meta.getFunInfo f.getAppFn').paramInfo
  return (pinfo.zip args).filterMap (λ arg => if arg.1.isExplicit then some arg.2 else none)

/-- try to close the goal using refl, return the `mvarId` if it fails-/
def tryRefl (goal : MVarId) : MetaM (Option MVarId) := do
  let res ← observing? do
    goal.refl
  if res == none then return some goal else return none

/-- to be moved somewhere else-/
def _root_.Lean.MVarId.applyWithFreshMVarLevels (goal : MVarId) (lem : Name) :
    MetaM (List MVarId) := do
  goal.apply (← mkConstWithFreshMVarLevels lem)

end util

private partial def telescopingFn (lem : Name) (goal : MVarId) (x : Expr) : MetaM MVarId := do
  let userName ← x.fvarId!.getUserName
  let newGoals ← goal.applyWithFreshMVarLevels lem
  if newGoals.length == 1 then
    let newGoal := newGoals[0]!
    return (← newGoal.intro userName).2
  throwTacticEx `congrm goal m!"failed to apply {lem}"

open private applyCongrThm? from Lean.Meta.Tactic.Congr in

/-- Main loop for `congrm` -/
partial def congrmLoop (pat : Expr) (goal : MVarId) : MetaM (List MVarId) := do
  -- Helper function (stolen from somewhere) that creates the correct FVars in `λ` and `∀`
  -- and does the recursion
  let binders (mvarId : MVarId) (n : Name) (xs : Array Expr) (k : Expr) : MetaM (List MVarId) := do
    congrmLoop k (← xs.foldlM (telescopingFn n) mvarId)
  if pat.isMVar then
    return [goal]
  else if pat.isForall then
    trace[congrm] s!"Forall pattern: {← ppExpr pat}"
    forallTelescope pat (binders goal ``pi_congr)
  else if pat.isLambda then
    trace[congrm] s!"Lambda pattern: {← ppExpr pat}"
    lambdaTelescope pat (binders goal ``funext)
  else if pat.isApp then
    let patternArgs := (← pat.getExplicitArgs).toList
    trace[congrm] s!"Apply pattern, fun: {← ppExpr pat.getAppFn}, args: {← patternArgs.mapM ppExpr}"
    let some congrThm ← mkCongrSimp? pat.getAppFn' (subsingletonInstImplicitRhs := false) |
      return []
    if pat.getAppFn.isMVar then
      -- If the function is a metavariable, we just return the goal
      return [goal]

    let goalArgs ← applyCongrThm? goal congrThm
    -- If the pattern has a different number of arguments, then we just fail:
    if goalArgs.length != patternArgs.length then
      trace[congrm] s!"Number of patterns and arguments are different:
        args: {goalArgs.map MVarId.name}
        pat: {← patternArgs.mapM ppExpr}"
      throwTacticEx `congrm goal m!"Number of function arguments does not match"

    -- Apply `congrm_loop` to all arguments with the corresponding pattern and concat the resulting
    -- list.
    return (← (patternArgs.zip goalArgs).mapM (λ (e,m) => congrmLoop e m)).join
  else if pat.isFVar then
    let fvarId := pat.fvarId!
    trace[congrm] s!"FVar: {← fvarId.getUserName}"
    let res ← observing? do
      goal.refl
    if res == none then
      throwTacticEx `congrm goal m!"Variable pattern is not proved by `refl`"
    else return []
  else
    trace[congrm] s!"We have an unhandled expression: {← ppExpr pat}"
    throwTacticEx `congrm goal m!"Invalid pattern"

/-- the core function for `congrm` -/
partial def congrmCore (pat : Expr) (goal : MVarId) : MetaM (List MVarId) := do
  -- First change `iff` to `=` and then run the loop:
  let mvars ← congrmLoop pat (← goal.iffOfEq)
  -- Try `refl` on all remaining goals
  mvars.filterMapM tryRefl

@[inherit_doc congrM]
elab_rules : tactic | `(tactic| congrm $expr:term) => withMainContext do
  liftMetaTactic <| congrmCore <| ← elabTerm expr none

/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Lean
import Mathlib.Tactic.Basic

/-!
The `check_equalities` tactic,
which checks the typing of equalities in the goal,
reporting discrepancies between the implicit type argument of the equality,
and the inferred types of the left and right hand sides,
at "instances and reducible" transparency.

Reports from this tactic do not necessarily indicate a problem,
although typically `simp` should reduce rather than increase the reported discrepancies.

`check_equalities` may be useful in diagnosing uses of `erw`.
-/

namespace Mathlib.Tactic.CheckEqualities

open Lean Meta Elab Tactic

/--
Find appearances of `@Eq α x y`, and apply `f` to each.
Return `true` if `f` returns `true` for at least one such appearance.
-/
def forEachEquality {ω m} [STWorld ω m] [MonadLiftT (ST ω) m] [Monad m]
    (e : Expr) (f : Expr → m Bool) : m Bool := do
  let (_, r) ← e.forEach (m := StateT Bool m) (fun e => do
    if e.isAppOfArity ``Eq 3 then do
      let r ← f e
      modify (fun b => b || r)) |>.run false
  return r

/-- Given an equality `@Eq α x y`,
infer the types of `x` and `y` and check whether these types agree,
at "instances and reducible" transparency, with `α`,
returning `true` if there are any discrepancies. -/
def checkEquality (e : Expr) : MetaM Bool := do
  withReducibleAndInstances do
  match_expr e with
  | Eq α x y =>
    let xα ← inferType x
    if !(← isDefEq α xα) then do
      logInfo m!"In equality{indentD e}\nthe inferred type of the left hand side\n\
        {x}\nis\n  {xα}\nbut should be\n  {α}"
      return true
    let yα ← inferType y
    if !(← isDefEq α yα) then do
      logInfo m!"In equality\n  {e}\nthe inferred type of the right hand side\n\
        {y}\nis\n  {yα}\nbut should be\n  {α}"
      return true
    return false
  | _ => throwError "{e} is not an equality."

/-- Check the typing of equalities in an expression, and return whether or not a
defeq problem was found. -/
def checkEqualities (e : Expr) : MetaM Bool := do
  forEachEquality e checkEquality

/-- Check the typing of equalities in the goal. -/
def checkEqualitiesTac : TacticM Unit := withMainContext do
  let e ← getMainTarget
  let r ← checkEqualities e
  -- If we printed a message, touch the main goal,
  -- so that the unused tactics linter does not complain.
  if r then touchMainGoal

/--
For each equality in the goal,
check the typing of the equality,
reporting discrepancies between the implicit type argument of the equality,
and the inferred types of the left and right hand sides,
at "instances and reducible" transparency.
-/
elab "#check_equalities" : tactic => checkEqualitiesTac

end Mathlib.Tactic.CheckEqualities

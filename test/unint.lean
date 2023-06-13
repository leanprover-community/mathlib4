import Mathlib.Tactic.unint

open Lean Expr Elab Tactic Meta

/-- Test that both `≠` and `¬` get interpreted as "negations". -/
example : (0 ≠ 1) = (¬ 0 = 1)  := by
  run_tac do
    if let some (_, lhs, rhs) := (← getMainTarget).eq? then
    let nelhs := ← lhs.getNeg
    let nerhs := ← rhs.getNeg
    guard <| nelhs == nerhs
    guard <| nelhs.1 == false
  rfl

private def myProp : Prop := ¬ True

/-- Test that `const`ants do not get unfolded, when using `getNeg`. -/
example (q : myProp) : myProp := by
  run_tac do
    let (notNot?, exp) := ← getNeg (← getMainTarget)
    let ft := ← ppExpr exp
    guard <| ft.pretty == "myProp"
    guard <| notNot? == true
  assumption

example (q : ¬ myProp) : ¬ myProp := by
  run_tac do
    let (notNot?, exp) := ← getNeg (← getMainTarget)
    let ft := ← ppExpr exp
    guard <| ft.pretty == "myProp"
    guard <| notNot? == false
  assumption

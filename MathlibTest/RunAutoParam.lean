import Mathlib.Tactic.RunAutoParam

open Mathlib.Meta

theorem cancel_self_div (x : Nat) (hx : x ≠ 0 := by grind) : x / x = 1 := by
  simp (disch:=grind)

example (x y : Nat) (hx : x ≠ 0) (hy : y ≠ 0) : (x + y) / (x + y) = 1 := by
  fail_if_success simp
  simp (disch:=run_auto_param) only [cancel_self_div]

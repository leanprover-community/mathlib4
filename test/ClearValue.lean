import Mathlib.Tactic.Basic

example : let x := 22; 0 ≤ x := by
  intro x
  clear_value x
  fail_if_success clear_value x
  exact Nat.zero_le _

example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  fail_if_success clear_value x
  clear_value y
  clear_value x
  fail_if_success clear_value x
  fail_if_success clear_value y
  exact y.2

example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  fail_if_success clear_value x
  clear_value y x
  fail_if_success clear_value x
  fail_if_success clear_value y
  exact y.2

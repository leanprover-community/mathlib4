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
  fail_if_success clear_value x -- 0 depends on `x = Nat.succ _`
  clear_value y x
  fail_if_success clear_value x
  fail_if_success clear_value y
  exact y.2

example : let x := 22; let y : Fin x := 0; y.1 < x := by
  intro x y
  fail_if_success clear_value x
  clear_value x y
  fail_if_success clear_value x
  fail_if_success clear_value y
  exact y.2

example : let x := 22; let y : Nat := x; let z : Fin (y + 1) := 0; z.1 < y + 1 := by
  intro x y z
  clear_value x -- `0` depends on `x` but its OK
  exact z.2

example : let x := 22; let y : Nat := x; let z : Fin (y + 1) := 0; z.1 < y + 1 := by
  intro x y z
  clear_value y -- `0` depends on `y` but its OK
  exact z.2

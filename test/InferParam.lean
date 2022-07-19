import Mathlib.Tactic.InferParam

namespace InferParamTest

theorem zero_le_add (a : Nat) (ha : 0 ≤ a := Nat.zero_le a) :
  0 ≤ a + a :=
calc
  0 ≤ a := ha
  _ ≤ a + a := Nat.le_add_left _ _

example : 0 ≤ 2 + 2 := by
  fail_if_success infer_opt_param
  decide

example : 0 ≤ 2 + 2 := by
  apply zero_le_add
  infer_opt_param

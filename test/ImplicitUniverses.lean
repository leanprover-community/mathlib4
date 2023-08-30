import Mathlib.Tactic.Basic
import Mathlib.Tactic.SuccessIfFailWithMsg

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example (x y : Type*) : sorry := by
  success_if_fail_with_msg
"type mismatch
  y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)" (exact x = y)
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example (x : Sort*) : sorry := by
  success_if_fail_with_msg
"type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1" (exact x = Prop)
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : sorry := by
  success_if_fail_with_msg
"type mismatch
  y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)" (exact ∀ x y : Type*, x = y)
  sorry

/-- warning: declaration uses 'sorry' -/
#guard_msgs in
example : sorry := by
 success_if_fail_with_msg
"type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1" (exact ∀ x : Sort*, x = Prop)
 sorry

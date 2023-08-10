import Mathlib.Tactic.Basic
import Mathlib.Tactic.SuccessIfFailWithMsg

example (x y : Type*) : sorry := by
  success_if_fail_with_msg
"type mismatch
  y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)" (exact x = y)
  sorry

example (x : Sort*) : sorry := by
  success_if_fail_with_msg
"type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1" (exact x = Prop)
  sorry

example : sorry := by
  success_if_fail_with_msg
"type mismatch
  y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)" (exact ∀ x y : Type*, x = y)
  sorry

example : sorry := by
 success_if_fail_with_msg
"type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1" (exact ∀ x : Sort*, x = Prop)
 sorry

import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.SuccessIfFailWithMsg

private axiom test_sorry : ∀ {α}, α
noncomputable example (_x _y : Type*) : test_sorry := by
  success_if_fail_with_msg
"type mismatch
  _y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)" (exact _x = _y)
  exact test_sorry

noncomputable example (_x : Sort*) : test_sorry := by
  success_if_fail_with_msg
"type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1" (exact _x = Prop)
  exact test_sorry

noncomputable example : test_sorry := by
  success_if_fail_with_msg
"type mismatch
  y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)" (exact ∀ x y : Type*, x = y)
  exact test_sorry

noncomputable example : test_sorry := by
  success_if_fail_with_msg
"type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1" (exact ∀ x : Sort*, x = Prop)
  exact test_sorry

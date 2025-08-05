import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.SuccessIfFailWithMsg

/--
error: type mismatch
  _y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)
-/
#guard_msgs in
noncomputable example (_x _y : Type*) : sorry := by
  exact _x = _y

/--
error: type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1
-/
#guard_msgs in
noncomputable example (_x : Sort*) : sorry := by
  exact _x = Prop

/--
error: type mismatch
  y
has type
  Type u_2 : Type (u_2 + 1)
but is expected to have type
  Type u_1 : Type (u_1 + 1)
-/
#guard_msgs in
noncomputable example : sorry := by
  exact ∀ x y : Type*, x = y

/--
error: type mismatch
  Prop
has type
  Type : Type 1
but is expected to have type
  Sort u_1 : Type u_1
-/
#guard_msgs in
noncomputable example : sorry := by
  exact ∀ x : Sort*, x = Prop

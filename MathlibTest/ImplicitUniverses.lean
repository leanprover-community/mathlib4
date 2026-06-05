module
import Mathlib.Tactic.SuccessIfFailWithMsg

/--
error: Type mismatch
  _y
has type
  Type u_2
of sort `Type (u_2 + 1)` but is expected to have type
  Type u_1
of sort `Type (u_1 + 1)`
-/
#guard_msgs in
noncomputable example (_x _y : Type*) : sorry := _x = _y

/--
error: Type mismatch
  Prop
has type
  Type
of sort `Type 1` but is expected to have type
  Sort u_1
of sort `Type u_1`
-/
#guard_msgs in
noncomputable example (_x : Sort*) : sorry := _x = Prop

/--
error: Type mismatch
  y
has type
  Type u_2
of sort `Type (u_2 + 1)` but is expected to have type
  Type u_1
of sort `Type (u_1 + 1)`
-/
#guard_msgs in
noncomputable example : sorry := ∀ x y : Type*, x = y

/--
error: Type mismatch
  Prop
has type
  Type
of sort `Type 1` but is expected to have type
  Sort u_1
of sort `Type u_1`
-/
#guard_msgs in
noncomputable example : sorry := ∀ x : Sort*, x = Prop

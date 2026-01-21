import Mathlib.Algebra.MonoidAlgebra.Defs

variable {R M A} [Semiring R] [Monoid M] [AddMonoid A]
section Notation
open scoped MonoidAlgebra AddMonoidAlgebra

-- TODO: could resolve ambiguity based on Monoid / AddMonoid
/--
error: Ambiguous term
  R[M]
Possible interpretations:
  R[M] : Type (max ?u.29 ?u.32)
  ⏎
  R[M] : Type (max ?u.29 ?u.32)
-/
#guard_msgs in
theorem test_1 : R[M] = MonoidAlgebra R M := rfl

/--
error: Ambiguous term
  R[A]
Possible interpretations:
  R[A] : Type (max ?u.86 ?u.92)
  ⏎
  R[A] : Type (max ?u.86 ?u.92)
-/
#guard_msgs in
theorem test_2 : R[A] = AddMonoidAlgebra R A := rfl

-- TODO: should round-trip.
/-- info: R[R] : Type u_1 -/
#guard_msgs in
#check AddMonoidAlgebra R R

/--
error: Ambiguous term
  R[R]
Possible interpretations:
  R[R] : Type ?u.164
  ⏎
  R[R] : Type ?u.164
-/
#guard_msgs in
#check R[R]

end Notation

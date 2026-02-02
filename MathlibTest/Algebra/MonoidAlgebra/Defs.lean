import Mathlib.Algebra.MonoidAlgebra.Defs

variable {R M A} [Semiring R] [Monoid M] [AddMonoid A]
section Notation
open scoped MonoidAlgebra AddMonoidAlgebra

set_option pp.mvars.anonymous false
-- TODO: could resolve ambiguity based on Monoid / AddMonoid
/--
error: Ambiguous term
  R[M]
Possible interpretations:
  R[M] : Type (max _ _)
  ⏎
  R[M] : Type (max _ _)
-/
#guard_msgs in
theorem test_1 : R[M] = MonoidAlgebra R M := rfl

/--
error: Ambiguous term
  R[A]
Possible interpretations:
  R[A] : Type (max _ _)
  ⏎
  R[A] : Type (max _ _)
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
  R[R] : Type _
  ⏎
  R[R] : Type _
-/
#guard_msgs in
#check R[R]

end Notation

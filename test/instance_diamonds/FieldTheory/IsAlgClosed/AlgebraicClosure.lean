import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

variable {k : Type*} [Field k]

example : (AddCommMonoid.natModule : Module ℕ (AlgebraicClosure k)) =
      @Algebra.toModule _ _ _ _ (AlgebraicClosure.instAlgebra k) := by
  with_reducible_and_instances rfl

example : (AddCommGroup.intModule _ : Module ℤ (AlgebraicClosure k)) =
      @Algebra.toModule _ _ _ _ (AlgebraicClosure.instAlgebra k) := by
  with_reducible_and_instances rfl

example [CharZero k] : AlgebraicClosure.instAlgebra k = algebraRat :=
  rfl
  -- TODO: by with_reducible_and_instances rfl fails

example : algebraInt (AlgebraicClosure ℚ) = AlgebraicClosure.instAlgebra ℚ :=
  rfl
  -- TODO: by with_reducible_and_instances rfl fails

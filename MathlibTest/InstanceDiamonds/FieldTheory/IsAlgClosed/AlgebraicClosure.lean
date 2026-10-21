module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

@[expose] public section

variable {k : Type*} [Field k]

example : (AddCommMonoid.toNatModule : Module ℕ (AlgebraicClosure k)) =
      @Algebra.toModule _ _ _ _ (AlgebraicClosure.instAlgebra k) := by
  with_reducible_and_instances rfl

example : (AddCommGroup.toIntModule _ : Module ℤ (AlgebraicClosure k)) =
      @Algebra.toModule _ _ _ _ (AlgebraicClosure.instAlgebra k) := by
  with_reducible_and_instances rfl

example [CharZero k] : AlgebraicClosure.instAlgebra k = DivisionRing.toRatAlgebra :=
  rfl
  -- TODO: by with_reducible_and_instances rfl fails

example : Ring.toIntAlgebra (AlgebraicClosure ℚ) = AlgebraicClosure.instAlgebra ℚ :=
  rfl
  -- TODO: by with_reducible_and_instances rfl fails

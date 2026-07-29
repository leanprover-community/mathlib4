import Mathlib.Algebra.Algebra.Rat

/-- The two `Algebra ℚ≥0 ℚ≥0` instances should coincide. -/
example : DivisionSemiring.toNNRatAlgebra = Algebra.id ℚ≥0 := rfl

/-- The two `Algebra ℚ ℚ` instances should coincide. -/
example : DivisionRing.toRatAlgebra = Algebra.id ℚ := rfl

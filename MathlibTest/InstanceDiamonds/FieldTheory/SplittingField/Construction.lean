import Mathlib.Algebra.Algebra.Rat
import Mathlib.FieldTheory.SplittingField.Construction

universe u v w

open Polynomial

variable {F : Type u} {K : Type v} {L : Type w}

variable [Field K] [Field L] [Field F]

variable (f : K[X])

-- The algebra instance deriving from `K` should be definitionally equal to that
-- deriving from the field structure on `SplittingField f`.
example :
    (AddCommMonoid.toNatModule : Module ℕ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.instAlgebra f) := by
  with_reducible_and_instances rfl

example :
    (AddCommGroup.toIntModule _ : Module ℤ (SplittingField f)) =
      @Algebra.toModule _ _ _ _ (SplittingField.instAlgebra f) := by
  with_reducible_and_instances rfl

example [CharZero K] : SplittingField.instAlgebra f = DivisionRing.toRatAlgebra :=
  rfl
  -- TODO: by with_reducible_and_instances rfl fails

example {q : ℚ[X]} : Ring.toIntAlgebra (SplittingField q) = SplittingField.instAlgebra q :=
  rfl
  -- TODO: by with_reducible_and_instances rfl fails

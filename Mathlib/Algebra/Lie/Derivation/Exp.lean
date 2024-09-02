import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup

namespace LieDerivation

universe u v

open algebraMap

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

noncomputable def exp : LieDerivation R L L → L →ₗ[R] L :=
  fun x ↦ ∑ n in Finset.range (nilpotencyClass x.toLinearMap),
    ((1 / n.factorial : ℚ) : R) • (x.toLinearMap ^ n)


end LieDerivation

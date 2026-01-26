import Mathlib.LinearAlgebra.InvariantBasisNumber
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Results relating rank and torsion.

-/

public section

variable {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M] [Module R M]

lemma rank_eq_zero_iff_isTorsion : Module.rank R M = 0 ↔ Module.IsTorsion R M := by
  rw [Module.IsTorsion, rank_eq_zero_iff]
  simp [mem_nonZeroDivisors_iff_ne_zero]

/-- The `StrongRankCondition` is automatic. See `commRing_strongRankCondition`. -/
theorem Module.finrank_eq_zero_iff_isTorsion [StrongRankCondition R] [Module.Finite R M] :
    finrank R M = 0 ↔ Module.IsTorsion R M := by
  rw [← rank_eq_zero_iff_isTorsion (R := R), ← finrank_eq_rank]
  norm_cast

import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup

namespace LieDerivation

universe u v

open algebraMap

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

-- TODO: figure out good generality for this..
-- Idea: Module over a ℚ-alg R, which is a ...? (Should be endomorphisms!)
-- Maybe best is just endomorphisms of some module of some ℚ-alg R?
noncomputable def expSum : (LieDerivation R L L) → L →ₗ[R] L := fun x ↦
  ∑ n in Finset.range (nilpotencyClass x.toLinearMap),
    ((1 / n.factorial : ℚ) : R) • (x.toLinearMap ^ n)

lemma expSum_eq_ge_range {x : LieDerivation R L L} (hx : IsNilpotent x.toLinearMap)
    {n : ℕ} (hn : nilpotencyClass x.toLinearMap ≤ n) :
    expSum R L x = ∑ i in Finset.range n, ((1 / i.factorial : ℚ) : R) • (x.toLinearMap ^ i) := by
  rw [← Finset.sum_range_add_sum_Ico _ hn, expSum, self_eq_add_right]
  apply Finset.sum_eq_zero
  rintro i hi
  apply smul_eq_zero_of_right
  apply pow_eq_zero_of_nilpotencyClass_le hx (Finset.mem_Ico.1 hi).1

lemma expSum_eq_range_add {x : LieDerivation R L L} (hx : IsNilpotent x.toLinearMap) {n : ℕ} :
    expSum R L x = ∑ i in Finset.range (nilpotencyClass x.toLinearMap + n),
      ((1 / i.factorial : ℚ) : R) • (x.toLinearMap ^ i) := by
  rw [expSum_eq_ge_range R L hx]
  exact Nat.le_add_right (nilpotencyClass x.toLinearMap) n


-- need nilpotencyClass smul le?

-- multiplicativity is needed here?
noncomputable def exp : (LieDerivation R L L) → L →ₗ⁅R⁆ L := fun δ ↦ {
  toLinearMap := expSum R L δ
  map_lie' := by
    intro x y
    simp [expSum]
    sorry -- need sum and ⁅⁆ interaction
    -- Then need some sort of "Finset.sum prod" interaction (probably have to do it manually)
    -- Then leibniz (done)
    -- then ok!


}

-- Also need sum version of Leibniz rule


end LieDerivation

import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup

namespace LieDerivation

universe u v

open algebraMap

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

noncomputable def expSum : (LieDerivation R L L) → L →ₗ[R] L := fun x ↦
  ∑ n in Finset.range (nilpotencyClass x.toLinearMap),
    ((1 / n.factorial : ℚ) : R) • (x.toLinearMap ^ n) -- TODO: get pow inside LieDerivation!!

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
noncomputable def exp : (LieDerivation R L L) → (L →ₗ[R] L)ˣ := fun x ↦
  { val := ∑ n in Finset.range (nilpotencyClass x.toLinearMap),
    ((1 / n.factorial : ℚ) : R) • (x.toLinearMap ^ n)
  -- todo do these later down
    inv := sorry
    val_inv := sorry
    inv_val := sorry }

-- Also need sum version of Leibniz rule


end LieDerivation

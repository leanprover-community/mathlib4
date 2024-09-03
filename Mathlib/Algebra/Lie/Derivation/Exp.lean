import Mathlib.Algebra.Lie.Derivation.Basic
import Mathlib.LinearAlgebra.GeneralLinearGroup

namespace LieDerivation

universe u v w

open algebraMap

section general_expSum

-- TODO: make `A` a `ℚ`-algebra immediately? (probably, just check it works in Lie case)
variable (R : Type u) (A : Type w) [CommRing R] [Algebra ℚ R] [Ring A] [Algebra R A]

noncomputable def expSum : A → A := fun x ↦
  ∑ n in Finset.range (nilpotencyClass x), ((1 / n.factorial : ℚ) : R) • (x ^ n)

/-- Auxillary definition to help define the inverse of `expSum` on nilpotent elements. -/
noncomputable def expSumRes : A → A := fun x ↦
  ∑ n in Finset.Ico 1 (nilpotencyClass x), ((1 / n.factorial : ℚ) : R) • (x ^ n)

/-- The inverse of `expSum` on nilpotent elements.

Note: takes the garbage value `0` for non-nilpotent elements. -/
noncomputable def expSumInv : A → A := fun x ↦
  ∑ n in Finset.range (nilpotencyClass x), (- 1)^n * (expSumRes R A x)

variable {A}

lemma expSum_eq_ge_range {x : A} (hx : IsNilpotent x) {n : ℕ} (hn : nilpotencyClass x ≤ n) :
    expSum R A x = ∑ i in Finset.range n, ((1 / i.factorial : ℚ) : R) • (x ^ i) := by
  rw [← Finset.sum_range_add_sum_Ico _ hn, expSum, self_eq_add_right]
  apply Finset.sum_eq_zero
  rintro i hi
  apply smul_eq_zero_of_right
  apply pow_eq_zero_of_nilpotencyClass_le hx (Finset.mem_Ico.1 hi).1

lemma expSum_eq_range_add {x : A} (hx : IsNilpotent x) {n : ℕ} :
    expSum R A x = ∑ i in Finset.range (nilpotencyClass x + n),
      ((1 / i.factorial : ℚ) : R) • (x ^ i) := by
  rw [expSum_eq_ge_range R hx]
  exact Nat.le_add_right (nilpotencyClass x) n

variable [Nontrivial A]

lemma expSum_eq_add_expSumRes {a : A} (ha : IsNilpotent a) :
    expSum R A a = 1 + expSumRes R A a := by
  rw [expSum, expSumRes, ← Finset.sum_range_add_sum_Ico _ (nilpotencyClass_pos ha)]
  simp

lemma asdf {a : A} (ha : IsNilpotent a) : (expSum R A a)*(expSumInv R A a) = 1 := by
  rw [expSumInv, expSum, expSumRes]
  simp
  sorry -- prove on paper first. this will be annoying

end general_expSum

variable (R : Type u) (L : Type v) [CommRing R] [Algebra ℚ R] [LieRing L] [LieAlgebra R L]

noncomputable def exp : (LieDerivation R L L) → L →ₗ⁅R⁆ L := fun δ ↦ {
  toLinearMap := expSum R (L →ₗ[R] L) δ
  map_lie' := by
    intro x y
    simp [expSum]
    sorry -- need sum and ⁅⁆ interaction
    -- Then need some sort of "Finset.sum prod" interaction (probably have to do it manually)
    -- Then leibniz (done)
    -- then ok!


}

/-
Next:
- Define inner automorphisms of a lie algebra (?)

-/


end LieDerivation

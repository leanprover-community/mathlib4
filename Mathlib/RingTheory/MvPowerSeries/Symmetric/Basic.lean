import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Rename

open Equiv (Perm)

variable {σ : Type*} {R : Type*} [CommSemiring R] [DecidableEq σ]

namespace MvPowerSeries

/-- A `MvPowerSeries φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation -/
def IsSymmetric (φ : MvPowerSeries σ R) : Prop :=
  ∀ e : Perm σ, rename e φ = φ

/-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
  ∃ n, ∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n

variable (σ R)

/-- The subalgebra of symmetric `MvPowerSeries`s. -/
def symmetricSubalgebra : Subalgebra R (MvPowerSeries σ R) where
  carrier := setOf IsSymmetric
  algebraMap_mem' r e := rename_C e r
  mul_mem' ha hb e := by simp only [map_mul, ha e, hb e]
  add_mem' ha hb e := by simp only [map_add, ha e, hb e]

/-- The subalgebra of symmetric `MvPowerSeries`s. -/
def boundedDegreeSubalgebra : Subalgebra R (MvPowerSeries σ R) where
  carrier := setOf HasBoundedDegree
  algebraMap_mem' r := by
    use 0
    intro s hs
    simp only [algebraMap_apply, Algebra.id.map_eq_id, RingHom.id_apply, ne_eq] at hs
    rw [← monomial_zero_eq_C, coeff_monomial] at hs
    simp only [ite_eq_right_iff, not_forall, exists_prop] at hs
    simp only [hs.left, Finsupp.sum_zero_index, le_refl]
  mul_mem' := by
    rintro a b ⟨na, ha⟩ ⟨nb, hb⟩
    use na + nb
    intro s hs
    rw [coeff_mul] at hs
    have (hps : Finset.antidiagonal s) : Finsupp.sum s (fun _ ↦ id) = (Finsupp.sum hps.1.1 (fun _ ↦ id) + Finsupp.sum hps.1.2 (fun _ ↦ id)) := by
      obtain ⟨p, hp⟩ := hps
      simp only [Finsupp.sum, id_eq]
      simp at hp
      rw [← hp]
      simp only [Finsupp.coe_add, Pi.add_apply, Finset.sum_add_distrib]
      have (f : σ →₀ ℕ) (A : Finset σ) (hA : f.support ⊆ A) : Finset.sum A f = Finset.sum f.support f := by
        rw [← finsum_eq_finset_sum_of_support_subset f _]
        rw [← finsum_eq_finset_sum_of_support_subset f _]
        simp only [Finsupp.fun_support_eq, Finset.coe_subset, Finset.Subset.refl]
        exact_mod_cast hA
      rw [this p.1 (p.1 + p.2).support _]
      rw [this p.2 (p.1 + p.2).support _]
      all_goals intro x hx; rw [Finsupp.mem_support_iff] at hx; rw [Finsupp.mem_support_iff]
      all_goals simp only [Finsupp.coe_add, Pi.add_apply, ne_eq, add_eq_zero, hx, and_false,
        not_false_eq_true]
      tauto
    have that : ∃ p : Finset.antidiagonal s, coeff R p.1.1 a * coeff R p.1.2 b ≠ 0 := by
      apply Finset.exists_ne_zero_of_sum_ne_zero at hs
      obtain ⟨p, hp⟩ := hs
      use ⟨p, hp.left⟩
      exact hp.right
    obtain ⟨p, hp⟩ := that
    rw [this p]
    gcongr
    · apply ha
      contrapose! hp
      rw [hp]
      exact zero_mul _
    · apply hb
      contrapose! hp
      rw [hp]
      exact mul_zero _
  add_mem' := by
    rintro a b ⟨na, ha⟩ ⟨nb, hb⟩
    use max na nb
    intro s hs
    rw [coeff_add] at hs
    have that : ∃ p : Finset.antidiagonal s, coeff R p.1.1 a + coeff R p.1.2 b ≠ 0 := by
      apply Finset.exists_ne_zero_of_sum_ne_zero at hs
      obtain ⟨p, hp⟩ := hs
      use ⟨p, hp.left⟩
      exact hp.right
    obtain ⟨p, hp⟩ := that
    rw [Finsupp.sum_add_distrib, Finsupp.sum_add_distrib] at hp
    rw [← hp]
    gcongr
    · apply ha
      contrapose! hp
      rw [hp]
      exact zero_add _
    · apply hb
      contrapose! hp
      rw [hp]
      exact add_zero _

end MvPowerSeries

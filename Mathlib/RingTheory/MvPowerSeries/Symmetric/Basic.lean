import Mathlib.Tactic.Basic
import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.RingTheory.MvPowerSeries.Degree
import Mathlib.RingTheory.MvPowerSeries.Rename

open Equiv (Perm)

variable {σ : Type*} {R : Type*} [CommSemiring R] [DecidableEq σ]

namespace MvPowerSeries

/-- A `MvPowerSeries φ` is symmetric if it is invariant under
permutations of its variables by the `rename` operation -/
def IsSymmetric (φ : MvPowerSeries σ R) : Prop :=
  ∀ e : Perm σ, renameEquiv e φ = φ

-- /-- A `MvPowerSeries φ` has bounded degree if its monomials are uniformly bounded -/
-- def HasBoundedDegree (φ : MvPowerSeries σ R) : Prop :=
--   ∃ n, ∀ s : σ →₀ ℕ, coeff R s φ ≠ 0 → s.sum (fun _ ↦ id) ≤ n

variable (σ R)

/-- The subalgebra of symmetric `MvPowerSeries`s. -/
def symmetricSubalgebra : Subalgebra R (MvPowerSeries σ R) where
  carrier := setOf IsSymmetric
  algebraMap_mem' r e := renameEquiv_C e r
  mul_mem' ha hb e := by simp only [map_mul, ha e, hb e]
  add_mem' ha hb e := by simp only [map_add, ha e, hb e]

/-- The subalgebra of symmetric `MvPowerSeries`s. -/
def boundedDegreeSubalgebra : Subalgebra R (MvPowerSeries σ R) where
  carrier := setOf HasBoundedDegree
  algebraMap_mem' r := by
    use 0
    rw [totalDegree_le_DegreeBound_iff]
    apply le_of_eq (totalDegree_C r)
  mul_mem' := by
    intro a b ⟨na, ha⟩ ⟨nb, hb⟩
    use na + nb
    rw [totalDegree_le_DegreeBound_iff] at *
    apply le_trans totalDegree_mul (add_le_add ha hb)
  add_mem' := by
    rintro a b ⟨na, ha⟩ ⟨nb, hb⟩
    use max na nb
    rw [totalDegree_le_DegreeBound_iff] at *
    apply le_trans totalDegree_add
    apply max_le
    · apply le_trans ha
      exact_mod_cast le_max_left na nb
    · apply le_trans hb
      exact_mod_cast le_max_right na nb

end MvPowerSeries

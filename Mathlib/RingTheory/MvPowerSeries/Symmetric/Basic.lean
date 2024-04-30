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
  ∃ n, ∀ s : σ →₀ ℕ, s ∈ φ.support → s.sum (fun _ ↦ id) ≤ n

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
    simp [algebraMap] at hs
    simp only [nonpos_iff_eq_zero]
    sorry
  mul_mem' ha hb := by
    have ⟨na, hna⟩ := ha
    have ⟨nb, hnb⟩ := hb
    use na + nb
    intro s hs
    sorry
  add_mem' ha hb := by sorry

end MvPowerSeries

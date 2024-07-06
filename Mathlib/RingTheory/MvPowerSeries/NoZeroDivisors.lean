/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.WellFounded

/-! # ZeroDivisors in a MvPowerSeries ring

- `mem_nonZeroDivisors_of_constantCoeff` proves that
a mv power series whose constant is not a zero divisor
is not a zero divisor

## TODO

Prove that if `R` has no zero divisors, then so does `MvPowerSeries σ R`
(To avoid induction, it would be nice to endow `σ →₀ ℕ
with a lexicographic order, for some well ordering of σ…)

-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- A multivariate power series is not a zero divisor
  when its constant coefficient is not a zero divisor -/
theorem mem_nonZeroDivisors_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff σ R φ ∈ nonZeroDivisors R) :
    φ ∈ nonZeroDivisors (MvPowerSeries σ R) := by
  rw [mem_nonZeroDivisors_iff]
  intro x hx
  letI : WellFoundedLT (σ →₀ ℕ) := Finsupp.wellFoundedLT'
  ext d
  simp only [map_zero]
  apply WellFoundedLT.induction d
  intro e he
  classical
  rw [← mul_right_mem_nonZeroDivisors_eq_zero_iff hφ]
  have := coeff_mul e x φ
  rw [hx, map_zero, Finset.sum_eq_single (e,0)] at this
  exact this.symm
  · rintro ⟨u,v⟩ huv huv'
    simp only [mem_antidiagonal] at huv
    simp only [ne_eq, Prod.mk.injEq, not_and] at huv'
    suffices u < e by simp only [he u this, zero_mul]
    rw [Finsupp.lt_def]
    have hue : u ≤ e := by simp only [← huv, le_add_iff_nonneg_right, zero_le]
    refine ⟨hue, ?_⟩
    by_contra h'
    suffices u = e by
      apply huv' this
      simpa only [← huv, self_eq_add_right] using this
    push_neg at h'
    exact le_antisymm hue h'
  · intro he
    simp only [mem_antidiagonal, add_zero, not_true_eq_false] at he

end Semiring

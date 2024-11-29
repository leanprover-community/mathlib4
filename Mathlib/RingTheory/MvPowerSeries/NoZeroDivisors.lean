/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finsupp.WellFounded
import Mathlib.RingTheory.MvPowerSeries.LexOrder

/-! # ZeroDivisors in a MvPowerSeries ring

- `mem_nonZeroDivisors_of_constantCoeff` proves that
a multivariate power series whose constant coefficient is not a zero divisor
is itself not a zero divisor

## TODO

* A subsequent PR #14571 proves that if `R` has no zero divisors,
then so does `MvPowerSeries σ R`.

* Transfer/adapt these results to `HahnSeries`.

## Remark

The analogue of `Polynomial.nmem_nonZeroDivisors_iff`
(McCoy theorem) holds for power series over a noetherian ring,
but not in general. See [Fields1971]
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
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero, ← mul_right_mem_nonZeroDivisors_eq_zero_iff hφ, ← map_zero (f := coeff R e), ← hx]
  convert (coeff_mul e x φ).symm
  rw [Finset.sum_eq_single (e,0), coeff_zero_eq_constantCoeff]
  · rintro ⟨u, _⟩ huv _
    suffices u < e by simp only [he u this, zero_mul, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_right, zero_le]
    · rintro rfl
      simp_all
  · simp only [mem_antidiagonal, add_zero, not_true_eq_false, coeff_zero_eq_constantCoeff,
      false_implies]

end Semiring

instance {σ R : Type*} [Semiring R] [NoZeroDivisors R] :
    NoZeroDivisors (MvPowerSeries σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    letI : LinearOrder σ := LinearOrder.swap σ WellOrderingRel.isWellOrder.linearOrder
    letI : WellFoundedGT σ := by
      change IsWellFounded σ fun x y ↦ WellOrderingRel x y
      exact IsWellOrder.toIsWellFounded
    simpa only [← lexOrder_eq_top_iff_eq_zero, lexOrder_mul, WithTop.add_eq_top] using h

end MvPowerSeries

end

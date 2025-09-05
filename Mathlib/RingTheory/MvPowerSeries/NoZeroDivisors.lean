/-
Copyright (c) 2024 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

import Mathlib.Data.Finsupp.WellFounded
import Mathlib.RingTheory.MvPowerSeries.LexOrder
import Mathlib.RingTheory.MvPowerSeries.Order

/-! # ZeroDivisors in a MvPowerSeries ring

- `mem_nonZeroDivisors_of_constantCoeff` proves that
a multivariate power series whose constant coefficient is not a zero divisor
is itself not a zero divisor


- `MvPowerSeries.order_mul` : multiplicativity of `MvPowerSeries.order`
  if the semiring `R` has no zero divisors

##  Instance

If `R` has `NoZeroDivisors`, then so does `MvPowerSeries σ R`.


## TODO

* Transfer/adapt these results to `HahnSeries`.

## Remark

The analogue of `Polynomial.notMem_nonZeroDivisors_iff`
(McCoy theorem) holds for power series over a Noetherian ring,
but not in general. See [Fields1971]
-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp nonZeroDivisors

variable {σ R : Type*}

section Semiring

variable [Semiring R]

theorem mem_nonZeroDivisorsRight_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ ∈ nonZeroDivisorsRight R) :
    φ ∈ nonZeroDivisorsRight (MvPowerSeries σ R) := by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero, ← mul_right_mem_nonZeroDivisorsRight_eq_zero_iff hφ,
    ← map_zero (f := coeff e), ← hx]
  convert (coeff_mul e x φ).symm
  rw [Finset.sum_eq_single (e, 0), coeff_zero_eq_constantCoeff]
  · rintro ⟨u, _⟩ huv _
    suffices u < e by simp only [he u this, zero_mul, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_right, zero_le]
    · rintro rfl
      simp_all
  · simp only [mem_antidiagonal, add_zero, not_true_eq_false, coeff_zero_eq_constantCoeff,
      false_implies]

-- TODO: derive from `mem_nonZeroDivisorsRight_of_constantCoeff` using `MulOpposite`
theorem mem_nonZeroDivisorsLeft_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ ∈ nonZeroDivisorsLeft R) :
    φ ∈ nonZeroDivisorsLeft (MvPowerSeries σ R) := by
  classical
  intro x hx
  ext d
  apply WellFoundedLT.induction d
  intro e he
  rw [map_zero, ← mul_left_mem_nonZeroDivisorsLeft_eq_zero_iff hφ,
    ← map_zero (f := coeff e), ← hx]
  convert (coeff_mul e φ x).symm
  rw [Finset.sum_eq_single (0, e), coeff_zero_eq_constantCoeff]
  · rintro ⟨_, u⟩ huv _
    suffices u < e by simp only [he u this, mul_zero, map_zero]
    apply lt_of_le_of_ne
    · simp only [← mem_antidiagonal.mp huv, le_add_iff_nonneg_left, zero_le]
    · rintro rfl
      simp_all
  · simp only [mem_antidiagonal, zero_add, not_true_eq_false, coeff_zero_eq_constantCoeff,
      false_implies]

/-- A multivariate power series is not a zero divisor
  when its constant coefficient is not a zero divisor -/
theorem mem_nonZeroDivisors_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff φ ∈ R⁰) :
    φ ∈ (MvPowerSeries σ R)⁰ :=
  ⟨mem_nonZeroDivisorsLeft_of_constantCoeff hφ.1, mem_nonZeroDivisorsRight_of_constantCoeff hφ.2⟩

lemma monomial_mem_nonzeroDivisorsLeft {n : σ →₀ ℕ} {r} :
    monomial n r ∈ nonZeroDivisorsLeft (MvPowerSeries σ R) ↔ r ∈ nonZeroDivisorsLeft R := by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_monomial_mul, if_pos le_add_self, add_tsub_cancel_right] at this
    simpa using H _ this

-- TODO: reduce duplication
lemma monomial_mem_nonzeroDivisorsRight {n : σ →₀ ℕ} {r} :
    monomial n r ∈ nonZeroDivisorsRight (MvPowerSeries σ R) ↔ r ∈ nonZeroDivisorsRight R := by
  constructor
  · intro H s hrs
    have := H (C s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff (i + n) $hrp)
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right] at this
    simpa using H _ this

lemma monomial_mem_nonzeroDivisors {n : σ →₀ ℕ} {r} :
    monomial n r ∈ (MvPowerSeries σ R)⁰ ↔ r ∈ R⁰ :=
  monomial_mem_nonzeroDivisorsLeft.and monomial_mem_nonzeroDivisorsRight

lemma X_mem_nonzeroDivisors {i : σ} :
    X i ∈ (MvPowerSeries σ R)⁰ := by
  rw [X, monomial_mem_nonzeroDivisors]
  exact Submonoid.one_mem R⁰

end Semiring

variable [Semiring R] [NoZeroDivisors R]

instance : NoZeroDivisors (MvPowerSeries σ R) where
  eq_zero_or_eq_zero_of_mul_eq_zero {φ ψ} h := by
    letI : LinearOrder σ := LinearOrder.swap σ WellOrderingRel.isWellOrder.linearOrder
    letI : WellFoundedGT σ := by
      change IsWellFounded σ fun x y ↦ WellOrderingRel x y
      exact IsWellOrder.toIsWellFounded
    simpa only [← lexOrder_eq_top_iff_eq_zero, lexOrder_mul, WithTop.add_eq_top] using h

theorem weightedOrder_mul (w : σ → ℕ) (f g : MvPowerSeries σ R) :
    (f * g).weightedOrder w = f.weightedOrder w + g.weightedOrder w := by
  apply le_antisymm _ (le_weightedOrder_mul w)
  by_cases hf : f.weightedOrder w < ⊤
  · by_cases hg : g.weightedOrder w < ⊤
    · let p := (f.weightedOrder w).toNat
      have hp : p = f.weightedOrder w := by
        simpa only [p, ENat.coe_toNat_eq_self, ← lt_top_iff_ne_top]
      let q := (g.weightedOrder w).toNat
      have hq : q = g.weightedOrder w := by
        simpa only [q, ENat.coe_toNat_eq_self, ← lt_top_iff_ne_top]
      have : f.weightedHomogeneousComponent w p * g.weightedHomogeneousComponent w q ≠ 0 := by
        simp only [ne_eq, mul_eq_zero]
        intro H
        rcases H with  H | H <;>
        · refine weightedHomogeneousComponent_of_weightedOrder ?_ H
          simp only [ENat.coe_toNat_eq_self, ne_eq, weightedOrder_eq_top_iff, p, q]
          rw [← ne_eq, ne_zero_iff_weightedOrder_finite w]
          exact ENat.coe_toNat (ne_top_of_lt (by simpa))
      rw [← weightedHomogeneousComponent_mul_of_le_weightedOrder
          (le_of_eq hp) (le_of_eq hq)] at this
      rw [← hp, ← hq, ← Nat.cast_add, ← not_lt]
      intro H
      apply this
      apply weightedHomogeneousComponent_of_lt_weightedOrder_eq_zero H
    · rw [not_lt_top_iff] at hg
      simp [hg]
  · rw [not_lt_top_iff] at hf
    simp [hf]

theorem order_mul (f g : MvPowerSeries σ R) :
    (f * g).order = f.order + g.order :=
  weightedOrder_mul _ f g

end MvPowerSeries

end

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

## TODO

* Transfer/adapt these results to `HahnSeries`.

## Remark

The analogue of `Polynomial.nmem_nonZeroDivisors_iff`
(McCoy theorem) holds for power series over a noetherian ring,
but not in general. See [Fields1971]
-/

noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp nonZeroDivisors

variable {σ R : Type*}

section Semiring

variable [Semiring R]

/-- A multivariate power series is not a zero divisor
  when its constant coefficient is not a zero divisor -/
theorem mem_nonZeroDivisors_of_constantCoeff {φ : MvPowerSeries σ R}
    (hφ : constantCoeff σ R φ ∈ R⁰) :
    φ ∈ (MvPowerSeries σ R)⁰ := by
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

lemma monomial_mem_nonzeroDivisors {n : σ →₀ ℕ} {r} :
    monomial R n r ∈ (MvPowerSeries σ R)⁰ ↔ r ∈ R⁰ := by
  simp only [mem_nonZeroDivisors_iff]
  constructor
  · intro H s hrs
    have := H (C _ _ s) (by rw [← monomial_zero_eq_C, monomial_mul_monomial]; ext; simp [hrs])
    simpa using congr(coeff _ 0 $(this))
  · intro H p hrp
    ext i
    have := congr(coeff _ (i + n) $hrp)
    rw [coeff_mul_monomial, if_pos le_add_self, add_tsub_cancel_right] at this
    simpa using H _ this

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
  classical
  apply le_antisymm _ (le_weightedOrder_mul w)
  by_cases hf : f.weightedOrder w < ⊤
  · by_cases hg : g.weightedOrder w < ⊤
    · let f' := f.weightedHomogeneousComponent w (f.weightedOrder w).toNat
      let g' := weightedHomogeneousComponent w (g.weightedOrder w).toNat g
      have hf'g' : f' * g' = (f * g).weightedHomogeneousComponent w
        ((f.weightedOrder w).toNat + (g.weightedOrder w).toNat) := by
        ext n
        simp only [f', g', coeff_mul, coeff_weightedHomogeneousComponent]
        split_ifs with hn
        · apply Finset.sum_congr rfl
          intro x hx
          rw [mem_antidiagonal] at hx
          rw [← hx, map_add] at hn
          suffices (weight w x.1 = (f.weightedOrder w).toNat ∧
              weight w x.2 = (g.weightedOrder w).toNat) ∨
            weight w x.1 < (f.weightedOrder w).toNat ∨
            weight w x.2 < (g.weightedOrder w).toNat by
              rcases this with h | h | h
              · rw [if_pos h.1, if_pos h.2]
              · suffices ↑(weight w x.1) < weightedOrder w f by
                  simp [if_neg (ne_of_lt h), f.coeff_eq_zero_of_lt_weightedOrder w this, zero_mul]
                rwa [← ENat.coe_toNat (LT.lt.ne_top hf), ENat.coe_lt_coe]
              · suffices ↑(weight w x.2) < weightedOrder w g by
                  simp [if_neg (ne_of_lt h), g.coeff_eq_zero_of_lt_weightedOrder w this, mul_zero]
                rwa [← ENat.coe_toNat (LT.lt.ne_top hg), ENat.coe_lt_coe]
          sorry
        · apply Finset.sum_eq_zero
          intro x hx
          rw [mem_antidiagonal] at hx
          split_ifs with h1 h2 <;>
            all_goals {
              try (simp only [mul_zero, zero_mul])
              try (exfalso; apply hn; rw [← h1, ← h2, ← map_add, hx]) }
      have f_ne_zero : f ≠ 0 := by
         rw [ne_zero_iff_weightedOrder_finite w]
         apply ENat.coe_toNat (LT.lt.ne_top hf)
      have f'_ne_zero : f' ≠ 0 := by
        simp only [ne_zero_iff_exists_coeff_ne_zero, f']
        obtain ⟨d, h⟩ := f.exists_coeff_ne_zero_and_weightedOrder
          w ((ne_zero_iff_weightedOrder_finite w).mp f_ne_zero)
        use d
        simp [← h.2, h.1, coeff_weightedHomogeneousComponent]
      have g_ne_zero : g ≠ 0 := by
         rw [ne_zero_iff_weightedOrder_finite w]
         apply ENat.coe_toNat (LT.lt.ne_top hg)
      simp only at hf hg
      have g'_ne_zero : g' ≠ 0 := by
        simp only [ne_zero_iff_exists_coeff_ne_zero, g']
        obtain ⟨d, h⟩ := g.exists_coeff_ne_zero_and_weightedOrder
          w ((ne_zero_iff_weightedOrder_finite w).mp g_ne_zero)
        use d
        simp [← h.2, h.1, coeff_weightedHomogeneousComponent]
      have : f' * g' ≠ 0 := (mul_ne_zero_iff_right g'_ne_zero).mpr f'_ne_zero
      rw [ne_zero_iff_exists_coeff_ne_zero] at this
      obtain ⟨d, hd⟩ := this
      simp only [hf'g', coeff_weightedHomogeneousComponent,
        ne_eq, ite_eq_right_iff, Classical.not_imp, f', g'] at hd
      have : weightedOrder w f + weightedOrder w g = weight w d := by
        rw [hd.1, ← ENat.coe_toNat (LT.lt.ne_top hf), ← ENat.coe_toNat (LT.lt.ne_top hg)]
        simp
      rw [this]
      apply weightedOrder_le
      exact hd.2
    · rw [not_lt_top_iff] at hg
      simp [hg]
  · rw [not_lt_top_iff] at hf
    simp [hf]

theorem order_mul (f g : MvPowerSeries σ R) :
    (f * g).order = f.order + g.order :=
  weightedOrder_mul _ f g


end MvPowerSeries

end

/-
Copyright (c) 2022 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!

A supplement to the file
# Mean value inequalities for integrals

In this file we prove some variants of Hölder's inequality for the Lebesgue integral `ℝ≥0∞` and
`ℝ≥0` functions; these will eventually join the main file.
-/

open scoped Classical BigOperators ENNReal
open Finset
set_option autoImplicit true

noncomputable section

variable {ι : Type*}

namespace Finset

lemma none_mem_insertNone {s : Finset α} : none ∈ insertNone s := by simp

lemma insertNone_nonempty {s : Finset α} : insertNone s |>.Nonempty := ⟨none, none_mem_insertNone⟩

end Finset

namespace Real

-- unused
-- theorem prod_rpow {ι} (s : Finset ι) {f : ι → ℝ} (hf : 0 ≤ f) (r : ℝ) :
--     ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r :=
--   finset_prod_rpow s f (fun i _ ↦ hf i) r

end Real

namespace ENNReal
open NNReal

theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

-- unused
theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i in s, f i ^ r = (∏ i in s, f i) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_lt_top h2f |>.ne

-- unused
theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i in s, (f i : ℝ≥0∞) ^ r = ((∏ i in s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  induction s using Finset.induction
  case empty => simp
  case insert i s hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

end ENNReal

namespace MeasureTheory

/-- A different formulation of Hölder's inequality for two functions -/
theorem _root_.ENNReal.lintegral_mul_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ≥0∞} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    {p q : ℝ} (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : p + q = 1) :
    ∫⁻ a, f a ^ p * g a ^ q ∂μ ≤ (∫⁻ a, f a ∂μ) ^ p * (∫⁻ a, g a ∂μ) ^ q := by
  rcases hp.eq_or_lt with rfl|hp
  · simp at hpq
    subst hpq
    simp
  rcases hq.eq_or_lt with rfl|hq
  · simp at hpq
    subst hpq
    simp
  have h2p : 1 < 1 / p
  · rw [one_div]
    apply one_lt_inv hp
    linarith
  have h2pq : 1 / (1 / p) + 1 / (1 / q) = 1
  · simp [hp.ne', hq.ne', hpq]
  have := ENNReal.lintegral_mul_le_Lp_mul_Lq μ ⟨h2p, h2pq⟩ (hf.pow_const p) (hg.pow_const q)
  simpa [← ENNReal.rpow_mul, hp.ne', hq.ne'] using this


@[to_additive]
theorem prod_insert_div [CommGroup β] [DecidableEq α] (ha : a ∉ s) {f : α → β} :
    (∏ x in insert a s, f x) / f a = ∏ x in s, f x := by simp [ha]

attribute [gcongr] ENNReal.rpow_le_rpow
/-- A version of Hölder with multiple arguments -/
theorem _root_.ENNReal.lintegral_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) (hs : s.Nonempty) {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {p : ι → ℝ} (hp : ∑ i in s, p i = 1) (h2p : ∀ i ∈ s, 0 ≤ p i) :
    ∫⁻ a, ∏ i in s, f i a ^ p i ∂μ ≤ ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
  induction s using Finset.induction generalizing p
  case empty =>
    simp at hs
  case insert i₀ s hi₀ ih =>
    rcases eq_or_ne (p i₀) 1 with h2i₀|h2i₀
    · simp [hi₀]
      have h2p : ∀ i ∈ s, p i = 0
      · simpa [hi₀, h2i₀, sum_eq_zero_iff_of_nonneg (fun i hi ↦ h2p i <| mem_insert_of_mem hi)]
          using hp
      calc ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, 1 ∂μ := by
            congr! 3 with x
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, 1 := by simp [h2i₀]
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
            congr 1
            apply prod_congr rfl fun i hi ↦ by rw [h2p i hi, ENNReal.rpow_zero]
    · have hs : s.Nonempty
      · rw [Finset.nonempty_iff_ne_empty]
        rintro rfl
        simp [h2i₀] at hp
      have hpi₀ : 0 ≤ 1 - p i₀
      · simp_rw [sub_nonneg, ← hp, single_le_sum h2p (mem_insert_self ..)]
      have h2pi₀ : 1 - p i₀ ≠ 0
      · rwa [sub_ne_zero, ne_comm]
      let q := fun i ↦ p i / (1 - p i₀)
      have hq : ∑ i in s, q i = 1
      · rw [← sum_div, ← sum_insert_sub hi₀, hp, div_self h2pi₀]
      have h2q : ∀ i ∈ s, 0 ≤ q i
      · exact fun i hi ↦ div_nonneg (h2p i <| mem_insert_of_mem hi) hpi₀
      calc ∫⁻ a, ∏ i in insert i₀ s, f i a ^ p i ∂μ
          = ∫⁻ a, f i₀ a ^ p i₀ * ∏ i in s, f i a ^ p i ∂μ := by simp [hi₀]
        _ = ∫⁻ a, f i₀ a ^ p i₀ * (∏ i in s, f i a ^ q i) ^ (1 - p i₀) ∂μ := by
            simp [← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel (h := h2pi₀)]
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∫⁻ a, ∏ i in s, f i a ^ q i ∂μ) ^ (1 - p i₀) := by
            apply ENNReal.lintegral_mul_norm_pow_le
            · exact hf i₀ <| mem_insert_self ..
            · exact s.aemeasurable_prod <| fun i hi ↦ (hf i <| mem_insert_of_mem hi).pow_const _
            · exact h2p i₀ <| mem_insert_self ..
            · exact hpi₀
            · apply add_sub_cancel'_right
        _ ≤ (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * (∏ i in s, (∫⁻ a, f i a ∂μ) ^ q i) ^ (1 - p i₀) := by
            gcongr -- behavior of gcongr is heartbeat-dependent, which makes code really fragile...
            exact ih hs (fun i hi ↦ hf i <| mem_insert_of_mem hi) hq h2q
        _ = (∫⁻ a, f i₀ a ∂μ) ^ p i₀ * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
            simp [← ENNReal.prod_rpow_of_nonneg hpi₀, ← ENNReal.rpow_mul,
              div_mul_cancel (h := h2pi₀)]
        _ = ∏ i in insert i₀ s, (∫⁻ a, f i a ∂μ) ^ p i := by simp [hi₀]

/-- A version of Hölder with multiple arguments, one of which plays a distinguished role. -/
theorem _root_.ENNReal.lintegral_mul_prod_norm_pow_le {α} [MeasurableSpace α] {μ : Measure α}
    (s : Finset ι) {g : α →  ℝ≥0∞} {f : ι → α → ℝ≥0∞} (hg : AEMeasurable g μ)
    (hf : ∀ i ∈ s, AEMeasurable (f i) μ) (q : ℝ) {p : ι → ℝ} (hpq : q + ∑ i in s, p i = 1)
    (hq :  0 ≤ q) (hp : ∀ i ∈ s, 0 ≤ p i) :
    ∫⁻ a, g a ^ q * ∏ i in s, f i a ^ p i ∂μ ≤
      (∫⁻ a, g a ∂μ) ^ q * ∏ i in s, (∫⁻ a, f i a ∂μ) ^ p i := by
  suffices
    ∫⁻ t, ∏ j in insertNone s, Option.elim j (g t) (fun j ↦ f j t) ^ Option.elim j q p ∂μ
    ≤ ∏ j in insertNone s, (∫⁻ t, Option.elim j (g t) (fun j ↦ f j t) ∂μ) ^ Option.elim j q p by
    simpa using this
  refine ENNReal.lintegral_prod_norm_pow_le _ insertNone_nonempty ?_ ?_ ?_
  · rintro (_|i) hi
    · exact hg
    · refine hf i ?_
      simpa using hi
  · simp_rw [sum_insertNone, Option.elim]
    exact hpq
  · rintro (_|i) hi
    · exact hq
    · refine hp i ?_
      simpa using hi

end MeasureTheory

/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Rémy Degenne
-/
import Mathlib.MeasureTheory.Integral.Lebesgue

/-!
# Lebesgue integral with respect to a σ-finite measure

In this file we prove several theorems about Lebesgue integral
that require the measure to be σ-finite.

These theorems were moved to a separate file because the main file became too long.
-/

open scoped Classical ENNReal NNReal
open Set hiding restrict restrict_apply

namespace MeasureTheory

local infixr:25 " →ₛ " => SimpleFunc

variable {α : Type*} {m : MeasurableSpace α}

/-- In a sigma-finite measure space, there exists an integrable function which is
positive everywhere (and with an arbitrarily small integral). -/
theorem exists_pos_lintegral_lt_of_sigmaFinite (μ : Measure α) [SigmaFinite μ] {ε : ℝ≥0∞}
    (ε0 : ε ≠ 0) : ∃ g : α → ℝ≥0, (∀ x, 0 < g x) ∧ Measurable g ∧ ∫⁻ x, g x ∂μ < ε := by
  /- Let `s` be a covering of `α` by pairwise disjoint measurable sets of finite measure. Let
    `δ : ℕ → ℝ≥0` be a positive function such that `∑' i, μ (s i) * δ i < ε`. Then the function that
     is equal to `δ n` on `s n` is a positive function with integral less than `ε`. -/
  set s : ℕ → Set α := disjointed (spanningSets μ)
  have : ∀ n, μ (s n) < ∞ := fun n =>
    (measure_mono <| disjointed_subset _ _).trans_lt (measure_spanningSets_lt_top μ n)
  obtain ⟨δ, δpos, δsum⟩ : ∃ δ : ℕ → ℝ≥0, (∀ i, 0 < δ i) ∧ (∑' i, μ (s i) * δ i) < ε :=
    ENNReal.exists_pos_tsum_mul_lt_of_countable ε0 _ fun n => (this n).ne
  set N : α → ℕ := spanningSetsIndex μ
  have hN_meas : Measurable N := measurable_spanningSetsIndex μ
  have hNs : ∀ n, N ⁻¹' {n} = s n := preimage_spanningSetsIndex_singleton μ
  refine ⟨δ ∘ N, fun x => δpos _, measurable_from_nat.comp hN_meas, ?_⟩
  erw [lintegral_comp measurable_from_nat.coe_nnreal_ennreal hN_meas]
  simpa [N, hNs, lintegral_countable', measurable_spanningSetsIndex, mul_comm] using δsum
#align measure_theory.exists_pos_lintegral_lt_of_sigma_finite MeasureTheory.exists_pos_lintegral_lt_of_sigmaFinite

section Trim

variable {m0 : MeasurableSpace α} {μ : Measure α}

theorem univ_le_of_forall_fin_meas_le (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : Set α → ℝ≥0∞} (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → f s ≤ C)
    (h_F_lim : ∀ S : ℕ → Set α, (∀ n, MeasurableSet[m] (S n)) → Monotone S →
      f (⋃ n, S n) ≤ ⨆ n, f (S n)) :
    f univ ≤ C := by
  let S := @spanningSets _ m (μ.trim hm) _
  have hS_mono : Monotone S := @monotone_spanningSets _ m (μ.trim hm) _
  have hS_meas : ∀ n, MeasurableSet[m] (S n) := @measurable_spanningSets _ m (μ.trim hm) _
  rw [← @iUnion_spanningSets _ m (μ.trim hm)]
  refine (h_F_lim S hS_meas hS_mono).trans ?_
  refine iSup_le fun n => hf (S n) (hS_meas n) ?_
  exact ((le_trim hm).trans_lt (@measure_spanningSets_lt_top _ m (μ.trim hm) _ n)).ne
#align measure_theory.univ_le_of_forall_fin_meas_le MeasureTheory.univ_le_of_forall_fin_meas_le

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. Version for a measurable function.
See `lintegral_le_of_forall_fin_meas_le'` for the more general `AEMeasurable` version. -/
theorem lintegral_le_of_forall_fin_meas_le_of_measurable (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : Measurable f)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  have : ∫⁻ x in univ, f x ∂μ = ∫⁻ x, f x ∂μ := by simp only [Measure.restrict_univ]
  rw [← this]
  refine univ_le_of_forall_fin_meas_le hm C hf fun S hS_meas hS_mono => ?_
  rw [← lintegral_indicator]
  swap
  · exact hm (⋃ n, S n) (@MeasurableSet.iUnion _ _ m _ _ hS_meas)
  have h_integral_indicator : ⨆ n, ∫⁻ x in S n, f x ∂μ = ⨆ n, ∫⁻ x, (S n).indicator f x ∂μ := by
    congr
    ext1 n
    rw [lintegral_indicator _ (hm _ (hS_meas n))]
  rw [h_integral_indicator, ← lintegral_iSup]
  · refine le_of_eq (lintegral_congr fun x => ?_)
    simp_rw [indicator_apply]
    by_cases hx_mem : x ∈ iUnion S
    · simp only [hx_mem, if_true]
      obtain ⟨n, hxn⟩ := mem_iUnion.mp hx_mem
      refine le_antisymm (_root_.trans ?_ (le_iSup _ n)) (iSup_le fun i => ?_)
      · simp only [hxn, le_refl, if_true]
      · by_cases hxi : x ∈ S i <;> simp [hxi]
    · simp only [hx_mem, if_false]
      rw [mem_iUnion] at hx_mem
      push_neg at hx_mem
      refine le_antisymm (zero_le _) (iSup_le fun n => ?_)
      simp only [hx_mem n, if_false, nonpos_iff_eq_zero]
  · exact fun n => hf_meas.indicator (hm _ (hS_meas n))
  · intro n₁ n₂ hn₁₂ a
    simp_rw [indicator_apply]
    split_ifs with h h_1
    · exact le_rfl
    · exact absurd (mem_of_mem_of_subset h (hS_mono hn₁₂)) h_1
    · exact zero_le _
    · exact le_rfl
#align measure_theory.lintegral_le_of_forall_fin_meas_le_of_measurable MeasureTheory.lintegral_le_of_forall_fin_meas_le_of_measurable

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure in a sub-σ-algebra and the measure is σ-finite on that sub-σ-algebra, then the integral
over the whole space is bounded by that same constant. -/
theorem lintegral_le_of_forall_fin_meas_le' {μ : Measure α} (hm : m ≤ m0) [SigmaFinite (μ.trim hm)]
    (C : ℝ≥0∞) {f : _ → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C := by
  let f' := hf_meas.mk f
  have hf' : ∀ s, MeasurableSet[m] s → μ s ≠ ∞ → ∫⁻ x in s, f' x ∂μ ≤ C := by
    refine fun s hs hμs => (le_of_eq ?_).trans (hf s hs hμs)
    refine lintegral_congr_ae (ae_restrict_of_ae (hf_meas.ae_eq_mk.mono fun x hx => ?_))
    dsimp only
    rw [hx]
  rw [lintegral_congr_ae hf_meas.ae_eq_mk]
  exact lintegral_le_of_forall_fin_meas_le_of_measurable hm C hf_meas.measurable_mk hf'
#align measure_theory.lintegral_le_of_forall_fin_meas_le' MeasureTheory.lintegral_le_of_forall_fin_meas_le'

end Trim

variable {μ : Measure α} [SigmaFinite μ]

/-- If the Lebesgue integral of a function is bounded by some constant on all sets with finite
measure and the measure is σ-finite, then the integral over the whole space is bounded by that same
constant. -/
theorem lintegral_le_of_forall_fin_meas_le (C : ℝ≥0∞) {f : α → ℝ≥0∞} (hf_meas : AEMeasurable f μ)
    (hf : ∀ s, MeasurableSet s → μ s ≠ ∞ → ∫⁻ x in s, f x ∂μ ≤ C) : ∫⁻ x, f x ∂μ ≤ C :=
  @lintegral_le_of_forall_fin_meas_le' _ _ _ _ _ (by rwa [trim_eq_self]) C _ hf_meas hf
#align measure_theory.lintegral_le_of_forall_fin_meas_le MeasureTheory.lintegral_le_of_forall_fin_meas_le

theorem SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral
    {f : α →ₛ ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  induction' f using MeasureTheory.SimpleFunc.induction with c s hs f₁ f₂ _ h₁ h₂ generalizing L
  · simp only [hs, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
      piecewise_eq_indicator, lintegral_indicator, lintegral_const, Measure.restrict_apply',
      ENNReal.coe_indicator, Function.const_apply] at hL
    have c_ne_zero : c ≠ 0 := by
      intro hc
      simp only [hc, ENNReal.coe_zero, zero_mul, ENNReal.not_lt_zero] at hL
    have : L / c < μ s := by
      rwa [ENNReal.div_lt_iff, mul_comm]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne, ENNReal.coe_ne_top, not_false_iff, true_or_iff]
    obtain ⟨t, ht, ts, mlt, t_top⟩ :
      ∃ t : Set α, MeasurableSet t ∧ t ⊆ s ∧ L / ↑c < μ t ∧ μ t < ∞ :=
      Measure.exists_subset_measure_lt_top hs this
    refine ⟨piecewise t ht (const α c) (const α 0), fun x => ?_, ?_, ?_⟩
    · refine indicator_le_indicator_of_subset ts (fun x => ?_) x
      exact zero_le _
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero, univ_inter,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', ENNReal.mul_lt_top ENNReal.coe_ne_top t_top.ne]
    · simp only [ht, const_zero, coe_piecewise, coe_const, SimpleFunc.coe_zero,
        piecewise_eq_indicator, ENNReal.coe_indicator, Function.const_apply, lintegral_indicator,
        lintegral_const, Measure.restrict_apply', univ_inter]
      rwa [mul_comm, ← ENNReal.div_lt_iff]
      · simp only [c_ne_zero, Ne, ENNReal.coe_eq_zero, not_false_iff, true_or_iff]
      · simp only [Ne, ENNReal.coe_ne_top, not_false_iff, true_or_iff]
  · replace hL : L < ∫⁻ x, f₁ x ∂μ + ∫⁻ x, f₂ x ∂μ := by
      rwa [← lintegral_add_left f₁.measurable.coe_nnreal_ennreal]
    by_cases hf₁ : ∫⁻ x, f₁ x ∂μ = 0
    · simp only [hf₁, zero_add] at hL
      rcases h₂ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_left, zero_le']
    by_cases hf₂ : ∫⁻ x, f₂ x ∂μ = 0
    · simp only [hf₂, add_zero] at hL
      rcases h₁ hL with ⟨g, g_le, g_top, gL⟩
      refine ⟨g, fun x => (g_le x).trans ?_, g_top, gL⟩
      simp only [SimpleFunc.coe_add, Pi.add_apply, le_add_iff_nonneg_right, zero_le']
    obtain ⟨L₁, L₂, hL₁, hL₂, hL⟩ :
      ∃ L₁ L₂ : ℝ≥0∞, (L₁ < ∫⁻ x, f₁ x ∂μ) ∧ (L₂ < ∫⁻ x, f₂ x ∂μ) ∧ L < L₁ + L₂ :=
      ENNReal.exists_lt_add_of_lt_add hL hf₁ hf₂
    rcases h₁ hL₁ with ⟨g₁, g₁_le, g₁_top, hg₁⟩
    rcases h₂ hL₂ with ⟨g₂, g₂_le, g₂_top, hg₂⟩
    refine ⟨g₁ + g₂, fun x => add_le_add (g₁_le x) (g₂_le x), ?_, ?_⟩
    · apply lt_of_le_of_lt _ (ENNReal.add_lt_top.2 ⟨g₁_top, g₂_top⟩)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      exact le_rfl
    · apply hL.trans ((ENNReal.add_lt_add hg₁ hg₂).trans_le _)
      rw [← lintegral_add_left g₁.measurable.coe_nnreal_ennreal]
      simp only [coe_add, Pi.add_apply, ENNReal.coe_add, le_rfl]
#align measure_theory.simple_func.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral

theorem exists_lt_lintegral_simpleFunc_of_lt_lintegral
    {f : α → ℝ≥0} {L : ℝ≥0∞} (hL : L < ∫⁻ x, f x ∂μ) :
    ∃ g : α →ₛ ℝ≥0, (∀ x, g x ≤ f x) ∧ ∫⁻ x, g x ∂μ < ∞ ∧ L < ∫⁻ x, g x ∂μ := by
  simp_rw [lintegral_eq_nnreal, lt_iSup_iff] at hL
  rcases hL with ⟨g₀, hg₀, g₀L⟩
  have h'L : L < ∫⁻ x, g₀ x ∂μ := by
    convert g₀L
    rw [← SimpleFunc.lintegral_eq_lintegral, SimpleFunc.coe_map]
    simp only [Function.comp_apply]
  rcases SimpleFunc.exists_lt_lintegral_simpleFunc_of_lt_lintegral h'L with ⟨g, hg, gL, gtop⟩
  exact ⟨g, fun x => (hg x).trans (ENNReal.coe_le_coe.1 (hg₀ x)), gL, gtop⟩
#align measure_theory.exists_lt_lintegral_simple_func_of_lt_lintegral MeasureTheory.exists_lt_lintegral_simpleFunc_of_lt_lintegral

end MeasureTheory

/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel
-/
import Mathlib.Analysis.NormedSpace.IndicatorFunction
import Mathlib.Data.Fintype.Order
import Mathlib.MeasureTheory.Function.AEEqFun
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub

/-!
# Basic theorems about ℒp space
-/
noncomputable section

open TopologicalSpace MeasureTheory Filter

open scoped NNReal ENNReal Topology ComplexConjugate

variable {α ε ε' E F G : Type*} {m m0 : MeasurableSpace α} {p : ℝ≥0∞} {q : ℝ} {μ ν : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] [ENorm ε] [ENorm ε']

namespace MeasureTheory

section Lp

section Top

theorem MemLp.eLpNorm_lt_top [TopologicalSpace ε] {f : α → ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ < ∞ :=
  hfp.2

theorem MemLp.eLpNorm_ne_top [TopologicalSpace ε] {f : α → ε} (hfp : MemLp f p μ) :
    eLpNorm f p μ ≠ ∞ :=
  ne_of_lt hfp.2

theorem lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top {f : α → ε} (hq0_lt : 0 < q)
    (hfq : eLpNorm' f q μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ q ∂μ < ∞ := by
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hq0_lt]
  exact ENNReal.rpow_lt_top_of_nonneg (le_of_lt hq0_lt) (ne_of_lt hfq)

theorem lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top {f : α → ε} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hfp : eLpNorm f p μ < ∞) : ∫⁻ a, ‖f a‖ₑ ^ p.toReal ∂μ < ∞ := by
  apply lintegral_rpow_enorm_lt_top_of_eLpNorm'_lt_top
  · exact ENNReal.toReal_pos hp_ne_zero hp_ne_top
  · simpa [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top] using hfp

theorem eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top {f : α → ε} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) : eLpNorm f p μ < ∞ ↔ ∫⁻ a, (‖f a‖ₑ) ^ p.toReal ∂μ < ∞ :=
  ⟨lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_ne_zero hp_ne_top, by
    intro h
    have hp' := ENNReal.toReal_pos hp_ne_zero hp_ne_top
    have : 0 < 1 / p.toReal := div_pos zero_lt_one hp'
    simpa [eLpNorm_eq_lintegral_rpow_enorm hp_ne_zero hp_ne_top] using
      ENNReal.rpow_lt_top_of_nonneg (le_of_lt this) (ne_of_lt h)⟩

end Top

section Zero

@[simp]
theorem eLpNorm'_exponent_zero {f : α → ε} : eLpNorm' f 0 μ = 1 := by
  rw [eLpNorm', div_zero, ENNReal.rpow_zero]

@[simp]
theorem eLpNorm_exponent_zero {f : α → ε} : eLpNorm f 0 μ = 0 := by simp [eLpNorm]

@[simp]
theorem memLp_zero_iff_aestronglyMeasurable [TopologicalSpace ε] {f : α → ε} :
    MemLp f 0 μ ↔ AEStronglyMeasurable f μ := by simp [MemLp, eLpNorm_exponent_zero]

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[simp]
theorem eLpNorm'_zero (hp0_lt : 0 < q) : eLpNorm' (0 : α → ε) q μ = 0 := by
  simp [eLpNorm'_eq_lintegral_enorm, hp0_lt]

@[simp]
theorem eLpNorm'_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) : eLpNorm' (0 : α → ε) q μ = 0 := by
  rcases le_or_gt 0 q with hq0 | hq_neg
  · exact eLpNorm'_zero (lt_of_le_of_ne hq0 hq0_ne.symm)
  · simp [eLpNorm'_eq_lintegral_enorm, hμ, hq_neg]

@[simp]
theorem eLpNormEssSup_zero : eLpNormEssSup (0 : α → ε) μ = 0 := by
  simp [eLpNormEssSup, ← bot_eq_zero', essSup_const_bot]

@[simp]
theorem eLpNorm_zero : eLpNorm (0 : α → ε) p μ = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp only [h_top, eLpNorm_exponent_top, eLpNormEssSup_zero]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, ENNReal.toReal_pos h0 h_top]

@[simp]
theorem eLpNorm_zero' : eLpNorm (fun _ : α => (0 : ε)) p μ = 0 := eLpNorm_zero

@[simp] lemma MemLp.zero : MemLp (0 : α → ε) p μ :=
  ⟨aestronglyMeasurable_zero, by rw [eLpNorm_zero]; exact ENNReal.coe_lt_top⟩

@[simp] lemma MemLp.zero' : MemLp (fun _ : α => (0 : ε)) p μ := MemLp.zero

variable [MeasurableSpace α]

theorem eLpNorm'_measure_zero_of_pos {f : α → ε} (hq_pos : 0 < q) :
    eLpNorm' f q (0 : Measure α) = 0 := by simp [eLpNorm', hq_pos]

theorem eLpNorm'_measure_zero_of_exponent_zero {f : α → ε} : eLpNorm' f 0 (0 : Measure α) = 1 := by
  simp [eLpNorm']

theorem eLpNorm'_measure_zero_of_neg {f : α → ε} (hq_neg : q < 0) :
    eLpNorm' f q (0 : Measure α) = ∞ := by simp [eLpNorm', hq_neg]

end ESeminormedAddMonoid

@[simp]
theorem eLpNormEssSup_measure_zero {f : α → ε} : eLpNormEssSup f (0 : Measure α) = 0 := by
  simp [eLpNormEssSup]

@[simp]
theorem eLpNorm_measure_zero {f : α → ε} : eLpNorm f p (0 : Measure α) = 0 := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top]
  rw [← Ne] at h0
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm', ENNReal.toReal_pos h0 h_top]

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

@[simp] lemma memLp_measure_zero {f : α → ε} : MemLp f p (0 : Measure α) := by
  simp [MemLp]

end ContinuousENorm

end Zero

section Neg

@[simp]
theorem eLpNorm'_neg (f : α → F) (q : ℝ) (μ : Measure α) : eLpNorm' (-f) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
theorem eLpNorm_neg (f : α → F) (p : ℝ≥0∞) (μ : Measure α) : eLpNorm (-f) p μ = eLpNorm f p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_eq_essSup_enorm]
  simp [eLpNorm_eq_eLpNorm' h0 h_top]

lemma eLpNorm_sub_comm (f g : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (f - g) p μ = eLpNorm (g - f) p μ := by simp [← eLpNorm_neg (f := f - g)]

theorem MemLp.neg {f : α → E} (hf : MemLp f p μ) : MemLp (-f) p μ :=
  ⟨AEStronglyMeasurable.neg hf.1, by simp [hf.right]⟩

theorem memLp_neg_iff {f : α → E} : MemLp (-f) p μ ↔ MemLp f p μ :=
  ⟨fun h => neg_neg f ▸ h.neg, MemLp.neg⟩

end Neg

section Const

variable {ε' ε'' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']
  [TopologicalSpace ε''] [ESeminormedAddMonoid ε'']

theorem eLpNorm'_const (c : ε) (hq_pos : 0 < q) :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm'_eq_lintegral_enorm, lintegral_const,
    ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ 1 / q)]
  congr
  rw [← ENNReal.rpow_mul]
  suffices hq_cancel : q * (1 / q) = 1 by rw [hq_cancel, ENNReal.rpow_one]
  rw [one_div, mul_inv_cancel₀ (ne_of_lt hq_pos).symm]

-- Generalising this to ESeminormedAddMonoid requires a case analysis whether ‖c‖ₑ = ⊤,
-- and will happen in a future PR.
theorem eLpNorm'_const' [IsFiniteMeasure μ] (c : F) (hc_ne_zero : c ≠ 0) (hq_ne_zero : q ≠ 0) :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ * μ Set.univ ^ (1 / q) := by
  rw [eLpNorm'_eq_lintegral_enorm, lintegral_const,
    ENNReal.mul_rpow_of_ne_top _ (measure_ne_top μ Set.univ)]
  · congr
    rw [← ENNReal.rpow_mul]
    suffices hp_cancel : q * (1 / q) = 1 by rw [hp_cancel, ENNReal.rpow_one]
    rw [one_div, mul_inv_cancel₀ hq_ne_zero]
  · have : ‖c‖ₑ ≠ 0 := by simp [hc_ne_zero]
    finiteness

theorem eLpNormEssSup_const (c : ε) (hμ : μ ≠ 0) : eLpNormEssSup (fun _ : α => c) μ = ‖c‖ₑ := by
  rw [eLpNormEssSup_eq_essSup_enorm, essSup_const _ hμ]

theorem eLpNorm'_const_of_isProbabilityMeasure (c : ε) (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' (fun _ : α => c) q μ = ‖c‖ₑ := by simp [eLpNorm'_const c hq_pos, measure_univ]

theorem eLpNorm_const (c : ε) (h0 : p ≠ 0) (hμ : μ ≠ 0) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  by_cases h_top : p = ∞
  · simp [h_top, eLpNormEssSup_const c hμ]
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

theorem eLpNorm_const' (c : ε) (h0 : p ≠ 0) (h_top : p ≠ ∞) :
    eLpNorm (fun _ : α => c) p μ = ‖c‖ₑ * μ Set.univ ^ (1 / ENNReal.toReal p) := by
  simp [eLpNorm_eq_eLpNorm' h0 h_top, eLpNorm'_const, ENNReal.toReal_pos h0 h_top]

-- NB. If ‖c‖ₑ = ∞ and μ is finite, this claim is false: the right has side is true,
-- but the left-hand side is false (as the norm is infinite).
theorem eLpNorm_const_lt_top_iff_enorm {c : ε''} (hc' : ‖c‖ₑ ≠ ∞)
    {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLpNorm (fun _ : α ↦ c) p μ < ∞ ↔ ‖c‖ₑ = 0 ∨ μ Set.univ < ∞ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp_ne_zero hp_ne_top
  by_cases hμ : μ = 0
  · simp only [hμ, Measure.coe_zero, Pi.zero_apply, or_true, ENNReal.zero_lt_top,
      eLpNorm_measure_zero]
  by_cases hc : ‖c‖ₑ = 0
  · rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_ne_zero hp_ne_top]
    simp [hc, ENNReal.zero_rpow_of_pos hp]
  rw [eLpNorm_const' c hp_ne_zero hp_ne_top]
  obtain hμ_top | hμ_ne_top := eq_or_ne (μ .univ) ∞
  · simp [hc, hμ_top, hp]
  rw [ENNReal.mul_lt_top_iff]
  simpa [hμ, hc, hμ_ne_top, hμ_ne_top.lt_top, hc'.lt_top] using by finiteness

theorem eLpNorm_const_lt_top_iff {p : ℝ≥0∞} {c : F} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    eLpNorm (fun _ : α => c) p μ < ∞ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [eLpNorm_const_lt_top_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

theorem memLp_const_enorm {c : ε'} (hc : ‖c‖ₑ ≠ ⊤) [IsFiniteMeasure μ] :
    MemLp (fun _ : α ↦ c) p μ := by
  refine ⟨aestronglyMeasurable_const, ?_⟩
  by_cases h0 : p = 0
  · simp [h0]
  by_cases hμ : μ = 0
  · simp [hμ]
  rw [eLpNorm_const c h0 hμ]
  finiteness

theorem memLp_const (c : E) [IsFiniteMeasure μ] : MemLp (fun _ : α => c) p μ :=
  memLp_const_enorm enorm_ne_top

theorem memLp_top_const_enorm {c : ε'} (hc : ‖c‖ₑ ≠ ⊤) :
    MemLp (fun _ : α ↦ c) ∞ μ :=
  ⟨aestronglyMeasurable_const, by by_cases h : μ = 0 <;> simp [eLpNorm_const _, h, hc.lt_top]⟩

theorem memLp_top_const (c : E) : MemLp (fun _ : α => c) ∞ μ :=
  memLp_top_const_enorm enorm_ne_top

theorem memLp_const_iff_enorm
    {p : ℝ≥0∞} {c : ε''} (hc : ‖c‖ₑ ≠ ⊤) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun _ : α ↦ c) p μ ↔ ‖c‖ₑ = 0 ∨ μ Set.univ < ∞ := by
  simp_all [MemLp, aestronglyMeasurable_const,
    eLpNorm_const_lt_top_iff_enorm hc hp_ne_zero hp_ne_top]

theorem memLp_const_iff {p : ℝ≥0∞} {c : E} (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞) :
    MemLp (fun _ : α => c) p μ ↔ c = 0 ∨ μ Set.univ < ∞ := by
  rw [memLp_const_iff_enorm enorm_ne_top hp_ne_zero hp_ne_top]; simp

end Const

variable {f : α → F}

lemma eLpNorm'_mono_enorm_ae {f : α → ε} {g : α → ε'} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ := by
  simp only [eLpNorm'_eq_lintegral_enorm]
  gcongr ?_ ^ (1/q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  gcongr

lemma eLpNorm'_mono_nnnorm_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ := by
  simp only [eLpNorm'_eq_lintegral_enorm]
  gcongr ?_ ^ (1/q)
  refine lintegral_mono_ae (h.mono fun x hx => ?_)
  dsimp [enorm]
  gcongr

theorem eLpNorm'_mono_ae {f : α → F} {g : α → G} (hq : 0 ≤ q) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm' f q μ ≤ eLpNorm' g q μ :=
  eLpNorm'_mono_enorm_ae hq (by simpa only [enorm_le_iff_norm_le] using h)

theorem eLpNorm'_congr_enorm_ae {f g : α → ε} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx ↦ by simp [hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]

theorem eLpNorm'_congr_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm' f q μ = eLpNorm' g q μ := by
  have : (‖f ·‖ₑ ^ q) =ᵐ[μ] (‖g ·‖ₑ ^ q) := hfg.mono fun x hx ↦ by simp [enorm, hx]
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_congr_ae this]

theorem eLpNorm'_congr_norm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx

theorem eLpNorm'_congr_ae {f g : α → ε} (hfg : f =ᵐ[μ] g) : eLpNorm' f q μ = eLpNorm' g q μ :=
  eLpNorm'_congr_enorm_ae (hfg.fun_comp _)

theorem eLpNormEssSup_congr_ae {f g : α → ε} (hfg : f =ᵐ[μ] g) :
    eLpNormEssSup f μ = eLpNormEssSup g μ :=
  essSup_congr_ae (hfg.fun_comp enorm)

theorem eLpNormEssSup_mono_enorm_ae {f g : α → ε} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNormEssSup f μ ≤ eLpNormEssSup g μ :=
  essSup_mono_ae <| hfg

theorem eLpNormEssSup_mono_nnnorm_ae {f g : α → F} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNormEssSup f μ ≤ eLpNormEssSup g μ :=
  essSup_mono_ae <| hfg.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

theorem eLpNorm_mono_enorm_ae {f : α → ε} {g : α → ε'} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm f p μ ≤ eLpNorm g p μ := by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact essSup_mono_ae h
  · exact eLpNorm'_mono_enorm_ae ENNReal.toReal_nonneg h

theorem eLpNorm_mono_nnnorm_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm f p μ ≤ eLpNorm g p μ := by
  simp only [eLpNorm]
  split_ifs
  · exact le_rfl
  · exact essSup_mono_ae (h.mono fun x hx => ENNReal.coe_le_coe.mpr hx)
  · exact eLpNorm'_mono_nnnorm_ae ENNReal.toReal_nonneg h

theorem eLpNorm_mono_ae {f : α → F} {g : α → G} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (by simpa only [enorm_le_iff_norm_le] using h)

theorem eLpNorm_mono_ae' {ε' : Type*} [ENorm ε']
    {f : α → ε} {g : α → ε'} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (by simpa only [enorm_le_iff_norm_le] using h)

theorem eLpNorm_mono_ae_real {f : α → F} {g : α → ℝ} (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae <| h.mono fun _x hx =>
    hx.trans ((le_abs_self _).trans (Real.norm_eq_abs _).symm.le)

theorem eLpNorm_mono_enorm {f : α → ε} {g : α → ε'} (h : ∀ x, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_enorm_ae (Eventually.of_forall h)

theorem eLpNorm_mono_nnnorm {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖₊ ≤ ‖g x‖₊) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_nnnorm_ae (Eventually.of_forall h)

theorem eLpNorm_mono {f : α → F} {g : α → G} (h : ∀ x, ‖f x‖ ≤ ‖g x‖) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae (Eventually.of_forall h)

theorem eLpNorm_mono_real {f : α → F} {g : α → ℝ} (h : ∀ x, ‖f x‖ ≤ g x) :
    eLpNorm f p μ ≤ eLpNorm g p μ :=
  eLpNorm_mono_ae_real (Eventually.of_forall h)

theorem eLpNormEssSup_le_of_ae_enorm_bound {f : α → ε} {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    eLpNormEssSup f μ ≤ C :=
  essSup_le_of_ae_le C hfC

theorem eLpNormEssSup_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNormEssSup f μ ≤ C :=
  essSup_le_of_ae_le (C : ℝ≥0∞) <| hfC.mono fun _x hx => ENNReal.coe_le_coe.mpr hx

theorem eLpNormEssSup_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormEssSup f μ ≤ ENNReal.ofReal C :=
  eLpNormEssSup_le_of_ae_nnnorm_bound <| hfC.mono fun _x hx => hx.trans C.le_coe_toNNReal

theorem eLpNormEssSup_lt_top_of_ae_enorm_bound {f : α → ε} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_enorm_bound hfC).trans_lt ENNReal.coe_lt_top

theorem eLpNormEssSup_lt_top_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_nnnorm_bound hfC).trans_lt ENNReal.coe_lt_top

theorem eLpNormEssSup_lt_top_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNormEssSup f μ < ∞ :=
  (eLpNormEssSup_le_of_ae_bound hfC).trans_lt ENNReal.ofReal_lt_top

theorem eLpNorm_le_of_ae_enorm_bound {ε} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    {f : α → ε} {C : ℝ≥0∞} (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) :
    eLpNorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖C‖ₑ := hfC.mono fun x hx ↦ hx.trans (Preorder.le_refl C)
  refine (eLpNorm_mono_enorm_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ), one_div, enorm_eq_self, smul_eq_mul]

theorem eLpNorm_le_of_ae_nnnorm_bound {f : α → F} {C : ℝ≥0} (hfC : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ C) :
    eLpNorm f p μ ≤ C • μ Set.univ ^ p.toReal⁻¹ := by
  rcases eq_zero_or_neZero μ with rfl | hμ
  · simp
  by_cases hp : p = 0
  · simp [hp]
  have : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ ‖(C : ℝ)‖₊ := hfC.mono fun x hx => hx.trans_eq C.nnnorm_eq.symm
  refine (eLpNorm_mono_ae this).trans_eq ?_
  rw [eLpNorm_const _ hp (NeZero.ne μ), C.enorm_eq, one_div, ENNReal.smul_def, smul_eq_mul]

theorem eLpNorm_le_of_ae_bound {f : α → F} {C : ℝ} (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    eLpNorm f p μ ≤ μ Set.univ ^ p.toReal⁻¹ * ENNReal.ofReal C := by
  rw [← mul_comm]
  exact eLpNorm_le_of_ae_nnnorm_bound (hfC.mono fun x hx => hx.trans C.le_coe_toNNReal)

theorem eLpNorm_congr_enorm_ae {f : α → ε} {g : α → ε'} (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_enorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_enorm_ae <| (EventuallyEq.symm hfg).le)

theorem eLpNorm_congr_nnnorm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ = ‖g x‖₊) :
    eLpNorm f p μ = eLpNorm g p μ :=
  le_antisymm (eLpNorm_mono_nnnorm_ae <| EventuallyEq.le hfg)
    (eLpNorm_mono_nnnorm_ae <| (EventuallyEq.symm hfg).le)

theorem eLpNorm_congr_norm_ae {f : α → F} {g : α → G} (hfg : ∀ᵐ x ∂μ, ‖f x‖ = ‖g x‖) :
    eLpNorm f p μ = eLpNorm g p μ :=
  eLpNorm_congr_nnnorm_ae <| hfg.mono fun _x hx => NNReal.eq hx

open scoped symmDiff in
theorem eLpNorm_indicator_sub_indicator (s t : Set α) (f : α → E) :
    eLpNorm (s.indicator f - t.indicator f) p μ = eLpNorm ((s ∆ t).indicator f) p μ :=
  eLpNorm_congr_norm_ae <| ae_of_all _ fun x ↦ by simp [Set.apply_indicator_symmDiff norm_neg]

@[simp]
theorem eLpNorm'_norm {f : α → F} : eLpNorm' (fun a => ‖f a‖) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
theorem eLpNorm'_enorm {f : α → ε} : eLpNorm' (fun a => ‖f a‖ₑ) q μ = eLpNorm' f q μ := by
  simp [eLpNorm'_eq_lintegral_enorm]

@[simp]
theorem eLpNorm_norm (f : α → F) : eLpNorm (fun x => ‖f x‖) p μ = eLpNorm f p μ :=
  eLpNorm_congr_norm_ae <| Eventually.of_forall fun _ => norm_norm _

@[simp]
theorem eLpNorm_enorm (f : α → ε) : eLpNorm (fun x ↦ ‖f x‖ₑ) p μ = eLpNorm f p μ :=
  eLpNorm_congr_enorm_ae <| Eventually.of_forall fun _ => enorm_enorm _

theorem eLpNorm'_enorm_rpow (f : α → ε) (p q : ℝ) (hq_pos : 0 < q) :
    eLpNorm' (‖f ·‖ₑ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, enorm_eq_self, ← ENNReal.rpow_mul, mul_comm]

/-- `f : α → ℝ` and `ENNReal.ofReal ∘ f : α → ℝ≥0∞` have the same `eLpNorm`.
Usually, you should not use this lemma (but use enorms everywhere.) -/
lemma eLpNorm_ofReal (f : α → ℝ) (hf : ∀ᵐ x ∂μ, 0 ≤ f x) :
    eLpNorm (ENNReal.ofReal ∘ f) p μ = eLpNorm f p μ :=
  eLpNorm_congr_enorm_ae <| hf.mono fun _x hx ↦ Real.enorm_ofReal_of_nonneg hx

theorem eLpNorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
    eLpNorm' (fun x => ‖f x‖ ^ q) p μ = eLpNorm' f (p * q) μ ^ q := by
  simp_rw [eLpNorm', ← ENNReal.rpow_mul, ← one_div_mul_one_div, one_div,
    mul_assoc, inv_mul_cancel₀ hq_pos.ne.symm, mul_one, ← ofReal_norm_eq_enorm,
    Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg (norm_nonneg _) _), mul_comm p,
    ← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]

theorem eLpNorm_enorm_rpow (f : α → ε) (hq_pos : 0 < q) :
    eLpNorm (‖f ·‖ₑ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, ENNReal.top_mul', hq_pos.not_ge,
      ENNReal.ofReal_eq_zero, if_false, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    have h_rpow : essSup (‖‖f ·‖ₑ ^ q‖ₑ) μ = essSup (‖f ·‖ₑ ^ q) μ := by congr
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => ‖f x‖ₑ) μ).symm
  rw [eLpNorm_eq_eLpNorm' h0 hp_top, eLpNorm_eq_eLpNorm' _ (by finiteness)]
  swap
  · refine mul_ne_zero h0 ?_
    rwa [Ne, ENNReal.ofReal_eq_zero, not_le]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq_pos.le]
  exact eLpNorm'_enorm_rpow f p.toReal q hq_pos

theorem eLpNorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
    eLpNorm (fun x => ‖f x‖ ^ q) p μ = eLpNorm f (p * ENNReal.ofReal q) μ ^ q := by
  rw [← eLpNorm_enorm_rpow f hq_pos]
  symm
  convert eLpNorm_ofReal (fun x ↦ ‖f x‖ ^ q) (by filter_upwards with x using by positivity)
  rw [Function.comp_apply, ← ofReal_norm_eq_enorm]
  exact ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity)

theorem eLpNorm_congr_ae {f g : α → ε} (hfg : f =ᵐ[μ] g) : eLpNorm f p μ = eLpNorm g p μ :=
  eLpNorm_congr_enorm_ae <| hfg.mono fun _x hx => hx ▸ rfl

theorem memLp_congr_ae [TopologicalSpace ε] {f g : α → ε} (hfg : f =ᵐ[μ] g) :
    MemLp f p μ ↔ MemLp g p μ := by
  simp only [MemLp, eLpNorm_congr_ae hfg, aestronglyMeasurable_congr hfg]

theorem MemLp.ae_eq [TopologicalSpace ε] {f g : α → ε} (hfg : f =ᵐ[μ] g) (hf_Lp : MemLp f p μ) :
    MemLp g p μ :=
  (memLp_congr_ae hfg).1 hf_Lp

section ContinuousENorm

variable {ε ε' : Type*}
  [TopologicalSpace ε] [TopologicalSpace ε'] [ContinuousENorm ε] [ContinuousENorm ε']

theorem MemLp.of_le_enorm {f : α → ε} {g : α → ε'} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_mono_ae' hfg).trans_lt hg.eLpNorm_lt_top⟩

theorem MemLp.of_le {f : α → E} {g : α → F} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) : MemLp f p μ :=
  ⟨hf, (eLpNorm_mono_ae hfg).trans_lt hg.eLpNorm_lt_top⟩

alias MemLp.mono := MemLp.of_le

theorem MemLp.mono'_enorm {f : α → ε} {g : α → ℝ≥0∞}
    (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ ≤ g a) : MemLp f p μ :=
  MemLp.of_le_enorm hg hf <| h.mono fun _x hx ↦ le_trans hx le_rfl

theorem MemLp.mono' {f : α → E} {g : α → ℝ} (hg : MemLp g p μ) (hf : AEStronglyMeasurable f μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ ≤ g a) : MemLp f p μ :=
  hg.of_le hf <| h.mono fun _x hx => le_trans hx (le_abs_self _)

theorem MemLp.congr_enorm {f : α → ε} {g : α → ε'} (hf : MemLp f p μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp g p μ :=
  hf.of_le_enorm hg <| EventuallyEq.le <| EventuallyEq.symm h

theorem MemLp.congr_norm {f : α → E} {g : α → F} (hf : MemLp f p μ) (hg : AEStronglyMeasurable g μ)
    (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp g p μ :=
  hf.mono hg <| EventuallyEq.le <| EventuallyEq.symm h

theorem memLp_congr_enorm {f : α → ε} {g : α → ε'} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ₑ = ‖g a‖ₑ) : MemLp f p μ ↔ MemLp g p μ :=
  ⟨fun h2f => h2f.congr_enorm hg h, fun h2g => h2g.congr_enorm hf <| EventuallyEq.symm h⟩

theorem memLp_congr_norm {f : α → E} {g : α → F} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ a ∂μ, ‖f a‖ = ‖g a‖) : MemLp f p μ ↔ MemLp g p μ :=
  ⟨fun h2f => h2f.congr_norm hg h, fun h2g => h2g.congr_norm hf <| EventuallyEq.symm h⟩

theorem memLp_top_of_bound_enorm {f : α → ε} (hf : AEStronglyMeasurable f μ) (C : ℝ≥0)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) : MemLp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_enorm_bound hfC⟩

theorem memLp_top_of_bound {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f ∞ μ :=
  ⟨hf, by
    rw [eLpNorm_exponent_top]
    exact eLpNormEssSup_lt_top_of_ae_bound hfC⟩

theorem MemLp.of_enorm_bound [IsFiniteMeasure μ] {f : α → ε} (hf : AEStronglyMeasurable f μ)
    {C : ℝ≥0∞} (hC : C ≠ ∞) (hfC : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ C) : MemLp f p μ := by
  apply (memLp_const_enorm hC).of_le_enorm (ε' := ℝ≥0∞) hf <| hfC.mono fun _x hx ↦ ?_
  rw [enorm_eq_self]; exact hx

theorem MemLp.of_bound [IsFiniteMeasure μ] {f : α → E} (hf : AEStronglyMeasurable f μ) (C : ℝ)
    (hfC : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : MemLp f p μ :=
  (memLp_const C).of_le hf (hfC.mono fun _x hx => le_trans hx (le_abs_self _))

theorem memLp_of_bounded [IsFiniteMeasure μ]
    {a b : ℝ} {f : α → ℝ} (h : ∀ᵐ x ∂μ, f x ∈ Set.Icc a b)
    (hX : AEStronglyMeasurable f μ) (p : ENNReal) : MemLp f p μ :=
  have ha : ∀ᵐ x ∂μ, a ≤ f x := h.mono fun ω h => h.1
  have hb : ∀ᵐ x ∂μ, f x ≤ b := h.mono fun ω h => h.2
  (memLp_const (max |a| |b|)).mono' hX (by filter_upwards [ha, hb] with x using abs_le_max_abs_abs)

@[gcongr, mono]
theorem eLpNorm'_mono_measure (f : α → ε) (hμν : ν ≤ μ) (hq : 0 ≤ q) :
    eLpNorm' f q ν ≤ eLpNorm' f q μ := by
  simp_rw [eLpNorm']
  gcongr

@[gcongr, mono]
theorem eLpNormEssSup_mono_measure (f : α → ε) (hμν : ν ≪ μ) :
    eLpNormEssSup f ν ≤ eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_mono_measure hμν

@[gcongr, mono]
theorem eLpNorm_mono_measure (f : α → ε) (hμν : ν ≤ μ) : eLpNorm f p ν ≤ eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_mono_measure f (Measure.absolutelyContinuous_of_le hμν)]
  simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  exact eLpNorm'_mono_measure f hμν ENNReal.toReal_nonneg

theorem MemLp.mono_measure {f : α → ε} (hμν : ν ≤ μ) (hf : MemLp f p μ) :
    MemLp f p ν :=
  ⟨hf.1.mono_measure hμν, (eLpNorm_mono_measure f hμν).trans_lt hf.2⟩

end ContinuousENorm

section Indicator

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
  {c : ε} {hf : AEStronglyMeasurable f μ} {s : Set α}
  {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']

lemma eLpNorm_indicator_eq_eLpNorm_restrict {f : α → ε} {s : Set α} (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) p μ = eLpNorm f p (μ.restrict s) := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm,
       enorm_indicator_eq_indicator_enorm, ENNReal.essSup_indicator_eq_essSup_restrict hs]
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top]
  suffices (∫⁻ x, (‖s.indicator f x‖ₑ) ^ p.toReal ∂μ) =
      ∫⁻ x in s, ‖f x‖ₑ ^ p.toReal ∂μ by rw [this]
  rw [← lintegral_indicator hs]
  congr
  simp_rw [enorm_indicator_eq_indicator_enorm]
  rw [eq_comm, ← Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal), Set.indicator_comp_of_zero,
    Function.comp_def]
  simp [ENNReal.toReal_pos hp_zero hp_top]

lemma eLpNormEssSup_indicator_eq_eLpNormEssSup_restrict (hs : MeasurableSet s) :
    eLpNormEssSup (s.indicator f) μ = eLpNormEssSup f (μ.restrict s) := by
  simp_rw [← eLpNorm_exponent_top, eLpNorm_indicator_eq_eLpNorm_restrict hs]

lemma eLpNorm_restrict_le (f : α → ε') (p : ℝ≥0∞) (μ : Measure α) (s : Set α) :
    eLpNorm f p (μ.restrict s) ≤ eLpNorm f p μ :=
  eLpNorm_mono_measure f Measure.restrict_le_self

lemma eLpNorm_indicator_le (f : α → ε) :
    eLpNorm (s.indicator f) p μ ≤ eLpNorm f p μ := by
  refine eLpNorm_mono_ae' <| .of_forall fun x ↦ ?_
  rw [enorm_indicator_eq_indicator_enorm]
  exact s.indicator_le_self _ x

lemma eLpNormEssSup_indicator_le (s : Set α) (f : α → ε) :
    eLpNormEssSup (s.indicator f) μ ≤ eLpNormEssSup f μ := by
  refine essSup_mono_ae (Eventually.of_forall fun x => ?_)
  simp_rw [enorm_indicator_eq_indicator_enorm]
  exact Set.indicator_le_self s _ x

lemma eLpNormEssSup_indicator_const_le (s : Set α) (c : ε) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ ≤ ‖c‖ₑ := by
  by_cases hμ0 : μ = 0
  · rw [hμ0, eLpNormEssSup_measure_zero]
    exact zero_le _
  · exact (eLpNormEssSup_indicator_le s fun _ => c).trans (eLpNormEssSup_const c hμ0).le

lemma eLpNormEssSup_indicator_const_eq (s : Set α) (c : ε) (hμs : μ s ≠ 0) :
    eLpNormEssSup (s.indicator fun _ : α => c) μ = ‖c‖ₑ := by
  refine le_antisymm (eLpNormEssSup_indicator_const_le s c) ?_
  by_contra! h
  have h' := ae_iff.mp (ae_lt_of_essSup_lt h)
  push_neg at h'
  refine hμs (measure_mono_null (fun x hx_mem => ?_) h')
  rw [Set.mem_setOf_eq, Set.indicator_of_mem hx_mem]

lemma eLpNorm_indicator_const₀ (hs : NullMeasurableSet s μ) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp hp_top
  calc
    eLpNorm (s.indicator fun _ => c) p μ
      = (∫⁻ x, (‖(s.indicator fun _ ↦ c) x‖ₑ ^ p.toReal) ∂μ) ^ (1 / p.toReal) :=
          eLpNorm_eq_lintegral_rpow_enorm hp hp_top
    _ = (∫⁻ x, (s.indicator fun _ ↦ ‖c‖ₑ ^ p.toReal) x ∂μ) ^ (1 / p.toReal) := by
      congr 2
      refine (Set.comp_indicator_const c (fun x ↦ (‖x‖ₑ) ^ p.toReal) ?_)
      simp [hp_pos]
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
      rw [lintegral_indicator_const₀ hs, ENNReal.mul_rpow_of_nonneg, ← ENNReal.rpow_mul,
        mul_one_div_cancel hp_pos.ne', ENNReal.rpow_one]
      positivity

lemma eLpNorm_indicator_const (hs : MeasurableSet s) (hp : p ≠ 0) (hp_top : p ≠ ∞) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) :=
  eLpNorm_indicator_const₀ hs.nullMeasurableSet hp hp_top

lemma eLpNorm_indicator_const' (hs : MeasurableSet s) (hμs : μ s ≠ 0) (hp : p ≠ 0) :
    eLpNorm (s.indicator fun _ => c) p μ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_indicator_const_eq s c hμs]
  · exact eLpNorm_indicator_const hs hp hp_top

variable (c) in
lemma eLpNorm_indicator_const_le (p : ℝ≥0∞) :
    eLpNorm (s.indicator fun _ => c) p μ ≤ ‖c‖ₑ * μ s ^ (1 / p.toReal) := by
  obtain rfl | hp := eq_or_ne p 0
  · simp only [eLpNorm_exponent_zero, zero_le']
  obtain rfl | h'p := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, ENNReal.toReal_top, _root_.div_zero, ENNReal.rpow_zero,
      mul_one]
    exact eLpNormEssSup_indicator_const_le _ _
  let t := toMeasurable μ s
  calc
    eLpNorm (s.indicator fun _ => c) p μ ≤ eLpNorm (t.indicator fun _ ↦ c) p μ :=
      eLpNorm_mono_enorm (enorm_indicator_le_of_subset (subset_toMeasurable _ _) _)
    _ = ‖c‖ₑ * μ t ^ (1 / p.toReal) :=
      eLpNorm_indicator_const (measurableSet_toMeasurable ..) hp h'p
    _ = ‖c‖ₑ * μ s ^ (1 / p.toReal) := by rw [measure_toMeasurable]

lemma MemLp.indicator {f : α → ε} (hs : MeasurableSet s) (hf : MemLp f p μ) :
    MemLp (s.indicator f) p μ :=
  ⟨hf.aestronglyMeasurable.indicator hs, lt_of_le_of_lt (eLpNorm_indicator_le f) hf.eLpNorm_lt_top⟩

lemma memLp_indicator_iff_restrict {f : α → ε} (hs : MeasurableSet s) :
    MemLp (s.indicator f) p μ ↔ MemLp f p (μ.restrict s) := by
  simp [MemLp, aestronglyMeasurable_indicator_iff hs, eLpNorm_indicator_eq_eLpNorm_restrict hs]

lemma memLp_indicator_const (p : ℝ≥0∞) (hs : MeasurableSet s) (c : E) (hμsc : c = 0 ∨ μ s ≠ ∞) :
    MemLp (s.indicator fun _ => c) p μ := by
  rw [memLp_indicator_iff_restrict hs]
  obtain rfl | hμ := hμsc
  · exact MemLp.zero
  · have := Fact.mk hμ.lt_top
    apply memLp_const

lemma eLpNormEssSup_piecewise (f g : α → ε) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    eLpNormEssSup (Set.piecewise s f g) μ
      = max (eLpNormEssSup f (μ.restrict s)) (eLpNormEssSup g (μ.restrict sᶜ)) := by
  simp only [eLpNormEssSup, ← ENNReal.essSup_piecewise hs]
  congr with x
  by_cases hx : x ∈ s <;> simp [hx]

lemma eLpNorm_top_piecewise (f g : α → ε) [DecidablePred (· ∈ s)] (hs : MeasurableSet s) :
    eLpNorm (Set.piecewise s f g) ∞ μ
      = max (eLpNorm f ∞ (μ.restrict s)) (eLpNorm g ∞ (μ.restrict sᶜ)) :=
  eLpNormEssSup_piecewise f g hs

protected lemma MemLp.piecewise {f : α → ε} [DecidablePred (· ∈ s)] {g} (hs : MeasurableSet s)
    (hf : MemLp f p (μ.restrict s)) (hg : MemLp g p (μ.restrict sᶜ)) :
    MemLp (s.piecewise f g) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, memLp_zero_iff_aestronglyMeasurable]
    exact AEStronglyMeasurable.piecewise hs hf.1 hg.1
  refine ⟨AEStronglyMeasurable.piecewise hs hf.1 hg.1, ?_⟩
  obtain rfl | hp_top := eq_or_ne p ∞
  · rw [eLpNorm_top_piecewise f g hs]
    exact max_lt hf.2 hg.2
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp_zero hp_top, ← lintegral_add_compl _ hs,
    ENNReal.add_lt_top]
  constructor
  · have h (x) (hx : x ∈ s) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖f x‖ₑ ^ p.toReal := by
      simp [hx]
    rw [setLIntegral_congr_fun hs h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hf.2
  · have h (x) (hx : x ∈ sᶜ) : ‖Set.piecewise s f g x‖ₑ ^ p.toReal = ‖g x‖ₑ ^ p.toReal := by
      have hx' : x ∉ s := hx
      simp [hx']
    rw [setLIntegral_congr_fun hs.compl h]
    exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp_zero hp_top hg.2

end Indicator

section ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

/-- For a function `f` with support in `s`, the Lᵖ norms of `f` with respect to `μ` and
`μ.restrict s` are the same. -/
theorem eLpNorm_restrict_eq_of_support_subset {s : Set α} {f : α → ε} (hsf : f.support ⊆ s) :
    eLpNorm f p (μ.restrict s) = eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp only [hp_top, eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    exact ENNReal.essSup_restrict_eq_of_support_subset fun x hx ↦ hsf <| enorm_ne_zero.1 hx
  · simp_rw [eLpNorm_eq_eLpNorm' hp0 hp_top, eLpNorm'_eq_lintegral_enorm]
    congr 1
    apply setLIntegral_eq_of_support_subset
    have : ¬(p.toReal ≤ 0) := by simpa only [not_le] using ENNReal.toReal_pos hp0 hp_top
    simpa [this] using hsf

end ENormedAddMonoid

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

theorem MemLp.restrict (s : Set α) {f : α → ε} (hf : MemLp f p μ) :
    MemLp f p (μ.restrict s) :=
  hf.mono_measure Measure.restrict_le_self

theorem eLpNorm'_smul_measure {p : ℝ} (hp : 0 ≤ p) {f : α → ε} (c : ℝ≥0∞) :
    eLpNorm' f p (c • μ) = c ^ (1 / p) * eLpNorm' f p μ := by
  simp [eLpNorm', ENNReal.mul_rpow_of_nonneg, hp]

end ContinuousENorm

section SMul
variable {R : Type*} [Zero R] [SMulWithZero R ℝ≥0∞] [IsScalarTower R ℝ≥0∞ ℝ≥0∞]
  [NoZeroSMulDivisors R ℝ≥0∞] {c : R}

@[simp] lemma eLpNormEssSup_smul_measure (hc : c ≠ 0) (f : α → ε) :
    eLpNormEssSup f (c • μ) = eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup]
  exact essSup_smul_measure hc _

end SMul

section ContinuousENorm

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]

/-- Use `eLpNorm_smul_measure_of_ne_top` instead. -/
private theorem eLpNorm_smul_measure_of_ne_zero_of_ne_top {p : ℝ≥0∞} (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) {f : α → ε} (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  simp_rw [eLpNorm_eq_eLpNorm' hp_ne_zero hp_ne_top]
  rw [eLpNorm'_smul_measure ENNReal.toReal_nonneg]
  congr
  simp_rw [one_div]
  rw [ENNReal.toReal_inv]

/-- See `eLpNorm_smul_measure_of_ne_zero'` for a version with scalar multiplication by `ℝ≥0`. -/
theorem eLpNorm_smul_measure_of_ne_zero {c : ℝ≥0∞} (hc : c ≠ 0) (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α) : eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hp_top : p = ∞
  · simp [hp_top, eLpNormEssSup_smul_measure hc]
  exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_top c

/-- See `eLpNorm_smul_measure_of_ne_zero` for a version with scalar multiplication by `ℝ≥0∞`. -/
lemma eLpNorm_smul_measure_of_ne_zero' {c : ℝ≥0} (hc : c ≠ 0) (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α) : eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ :=
  (eLpNorm_smul_measure_of_ne_zero (ENNReal.coe_ne_zero.2 hc) ..).trans (by simp; norm_cast)

/-- See `eLpNorm_smul_measure_of_ne_top'` for a version with scalar multiplication by `ℝ≥0`. -/
theorem eLpNorm_smul_measure_of_ne_top {p : ℝ≥0∞} (hp_ne_top : p ≠ ∞) (f : α → ε) (c : ℝ≥0∞) :
    eLpNorm f p (c • μ) = c ^ (1 / p).toReal • eLpNorm f p μ := by
  by_cases hp0 : p = 0
  · simp [hp0]
  · exact eLpNorm_smul_measure_of_ne_zero_of_ne_top hp0 hp_ne_top c

/-- See `eLpNorm_smul_measure_of_ne_top'` for a version with scalar multiplication by `ℝ≥0∞`. -/
lemma eLpNorm_smul_measure_of_ne_top' (hp : p ≠ ∞) (c : ℝ≥0) (f : α → ε) :
    eLpNorm f p (c • μ) = c ^ p.toReal⁻¹ • eLpNorm f p μ := by
  have : 0 ≤ p.toReal⁻¹ := by positivity
  refine (eLpNorm_smul_measure_of_ne_top hp ..).trans ?_
  simp [ENNReal.smul_def, ENNReal.coe_rpow_of_nonneg, this]

theorem eLpNorm_one_smul_measure {f : α → ε} (c : ℝ≥0∞) :
    eLpNorm f 1 (c • μ) = c * eLpNorm f 1 μ := by
  rw [eLpNorm_smul_measure_of_ne_top] <;> simp

theorem MemLp.of_measure_le_smul {μ' : Measure α} {c : ℝ≥0∞} (hc : c ≠ ∞)
    (hμ'_le : μ' ≤ c • μ) {f : α → ε} (hf : MemLp f p μ) : MemLp f p μ' := by
  refine ⟨hf.1.mono_ac (Measure.absolutelyContinuous_of_le_smul hμ'_le), ?_⟩
  refine (eLpNorm_mono_measure f hμ'_le).trans_lt ?_
  by_cases hc0 : c = 0
  · simp [hc0]
  rw [eLpNorm_smul_measure_of_ne_zero hc0, smul_eq_mul]
  refine ENNReal.mul_lt_top (Ne.lt_top ?_) hf.2
  simp [hc, hc0]

theorem MemLp.smul_measure {f : α → ε} {c : ℝ≥0∞} (hf : MemLp f p μ) (hc : c ≠ ∞) :
    MemLp f p (c • μ) :=
  hf.of_measure_le_smul hc le_rfl

variable {ε : Type*} [ENorm ε] in
theorem eLpNorm_one_add_measure (f : α → ε) (μ ν : Measure α) :
    eLpNorm f 1 (μ + ν) = eLpNorm f 1 μ + eLpNorm f 1 ν := by
  simp_rw [eLpNorm_one_eq_lintegral_enorm]
  rw [lintegral_add_measure _ μ ν]

theorem eLpNorm_le_add_measure_right (f : α → ε) (μ ν : Measure α) {p : ℝ≥0∞} :
    eLpNorm f p μ ≤ eLpNorm f p (μ + ν) :=
  eLpNorm_mono_measure f <| Measure.le_add_right <| le_refl _

theorem eLpNorm_le_add_measure_left (f : α → ε) (μ ν : Measure α) {p : ℝ≥0∞} :
    eLpNorm f p ν ≤ eLpNorm f p (μ + ν) :=
  eLpNorm_mono_measure f <| Measure.le_add_left <| le_refl _

variable {ε : Type*} [ENorm ε] in
lemma eLpNormEssSup_eq_iSup (hμ : ∀ a, μ {a} ≠ 0) (f : α → ε) : eLpNormEssSup f μ = ⨆ a, ‖f a‖ₑ :=
  essSup_eq_iSup hμ _

variable {ε : Type*} [ENorm ε] in
@[simp] lemma eLpNormEssSup_count [MeasurableSingletonClass α] (f : α → ε) :
    eLpNormEssSup f .count = ⨆ a, ‖f a‖ₑ := essSup_count _

theorem MemLp.left_of_add_measure {f : α → ε} (h : MemLp f p (μ + ν)) :
    MemLp f p μ :=
  h.mono_measure <| Measure.le_add_right <| le_refl _

theorem MemLp.right_of_add_measure {f : α → ε} (h : MemLp f p (μ + ν)) :
    MemLp f p ν :=
  h.mono_measure <| Measure.le_add_left <| le_refl _

theorem MemLp.enorm {f : α → ε} (h : MemLp f p μ) : MemLp (‖f ·‖ₑ) p μ :=
  ⟨h.aestronglyMeasurable.enorm.aestronglyMeasurable,
    by simp_rw [MeasureTheory.eLpNorm_enorm, h.eLpNorm_lt_top]⟩

theorem MemLp.norm {f : α → E} (h : MemLp f p μ) : MemLp (fun x => ‖f x‖) p μ :=
  h.of_le h.aestronglyMeasurable.norm (Eventually.of_forall fun x => by simp)

theorem memLp_enorm_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    MemLp (‖f ·‖ₑ) p μ ↔ MemLp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_enorm]; exact h.2⟩, fun h => h.enorm⟩

theorem memLp_norm_iff {f : α → E} (hf : AEStronglyMeasurable f μ) :
    MemLp (fun x => ‖f x‖) p μ ↔ MemLp f p μ :=
  ⟨fun h => ⟨hf, by rw [← eLpNorm_norm]; exact h.2⟩, fun h => h.norm⟩

end ContinuousENorm

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

theorem eLpNorm'_eq_zero_of_ae_zero {f : α → ε} (hq0_lt : 0 < q) (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero hq0_lt]

theorem eLpNorm'_eq_zero_of_ae_zero' (hq0_ne : q ≠ 0) (hμ : μ ≠ 0) {f : α → ε}
    (hf_zero : f =ᵐ[μ] 0) :
    eLpNorm' f q μ = 0 := by rw [eLpNorm'_congr_ae hf_zero, eLpNorm'_zero' hq0_ne hμ]

theorem eLpNorm_eq_zero_of_ae_zero {f : α → ε} (hf : f =ᵐ[μ] 0) : eLpNorm f p μ = 0 := by
  rw [← eLpNorm_zero (p := p) (μ := μ) (α := α) (ε := ε)]
  exact eLpNorm_congr_ae hf

theorem eLpNorm'_eq_zero_of_ae_eq_zero {f : α → ε} {p : ℝ} (hp : 0 < p)
    (hf : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = 0) : eLpNorm' f p μ = 0 := by
  rw [← eLpNorm'_zero hp (μ := μ) (ε := ε), eLpNorm'_congr_enorm_ae]
  simp only [hf, Pi.zero_apply, enorm_zero]

variable {ε : Type*} [ENorm ε] in
theorem ae_le_eLpNormEssSup {f : α → ε} : ∀ᵐ y ∂μ, ‖f y‖ₑ ≤ eLpNormEssSup f μ :=
  ae_le_essSup

-- NB. Changing this lemma to use ‖‖ₑ makes it false (only => still holds);
-- unlike a nnnorm, the enorm can be ∞.
lemma eLpNormEssSup_lt_top_iff_isBoundedUnder :
    eLpNormEssSup f μ < ⊤ ↔ IsBoundedUnder (· ≤ ·) (ae μ) fun x ↦ ‖f x‖₊ where
  mp h := ⟨(eLpNormEssSup f μ).toNNReal, by
    simp_rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal h.ne]; exact ae_le_eLpNormEssSup⟩
  mpr := by rintro ⟨C, hC⟩; exact eLpNormEssSup_lt_top_of_ae_nnnorm_bound (C := C) hC

variable {ε : Type*} [ENorm ε] in
theorem meas_eLpNormEssSup_lt {f : α → ε} : μ { y | eLpNormEssSup f μ < ‖f y‖ₑ } = 0 :=
  meas_essSup_lt

lemma eLpNorm_lt_top_of_finite [Finite α] [IsFiniteMeasure μ] : eLpNorm f p μ < ∞ := by
  obtain rfl | hp₀ := eq_or_ne p 0
  · simp
  obtain rfl | hp := eq_or_ne p ∞
  · simp only [eLpNorm_exponent_top, eLpNormEssSup_lt_top_iff_isBoundedUnder]
    exact .le_of_finite
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp]
  refine IsFiniteMeasure.lintegral_lt_top_of_bounded_to_ennreal μ ?_
  simp_rw [enorm, ← ENNReal.coe_rpow_of_nonneg _ ENNReal.toReal_nonneg]
  norm_cast
  exact Finite.exists_le _

@[simp] lemma MemLp.of_discrete [DiscreteMeasurableSpace α] [Finite α] [IsFiniteMeasure μ] :
    MemLp f p μ :=
  let ⟨C, hC⟩ := Finite.exists_le (‖f ·‖₊); .of_bound .of_discrete C <| .of_forall hC

@[simp] lemma eLpNorm_of_isEmpty [IsEmpty α] (f : α → ε) (p : ℝ≥0∞) : eLpNorm f p μ = 0 := by
  simp [Subsingleton.elim f 0]

end ESeminormedAddMonoid

section ENormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]

theorem ae_eq_zero_of_eLpNorm'_eq_zero {f : α → ε} (hq0 : 0 ≤ q) (hf : AEStronglyMeasurable f μ)
    (h : eLpNorm' f q μ = 0) : f =ᵐ[μ] 0 := by
  simp only [eLpNorm'_eq_lintegral_enorm, lintegral_eq_zero_iff' (hf.enorm.pow_const q), one_div,
    ENNReal.rpow_eq_zero_iff, inv_pos, inv_neg'', hq0.not_gt, and_false, or_false] at h
  refine h.left.mono fun x hx ↦ ?_
  simp only [Pi.ofNat_apply, ENNReal.rpow_eq_zero_iff, enorm_eq_zero, h.2.not_gt, and_false,
    or_false] at hx
  simp [hx.1]

theorem eLpNorm'_eq_zero_iff (hq0_lt : 0 < q) {f : α → ε} (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f q μ = 0 ↔ f =ᵐ[μ] 0 :=
  ⟨ae_eq_zero_of_eLpNorm'_eq_zero (le_of_lt hq0_lt) hf, eLpNorm'_eq_zero_of_ae_zero hq0_lt⟩

variable {ε : Type*} [ENorm ε] in
theorem enorm_ae_le_eLpNormEssSup {_ : MeasurableSpace α} (f : α → ε) (μ : Measure α) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ eLpNormEssSup f μ :=
  ENNReal.ae_le_essSup fun x => ‖f x‖ₑ

@[deprecated (since := "2025-03-05")] alias
coe_nnnorm_ae_le_eLpNormEssSup := enorm_ae_le_eLpNormEssSup

@[simp]
theorem eLpNormEssSup_eq_zero_iff {f : α → ε} : eLpNormEssSup f μ = 0 ↔ f =ᵐ[μ] 0 := by
  simp [EventuallyEq, eLpNormEssSup_eq_essSup_enorm]

theorem eLpNorm_eq_zero_iff {f : α → ε} (hf : AEStronglyMeasurable f μ) (h0 : p ≠ 0) :
    eLpNorm f p μ = 0 ↔ f =ᵐ[μ] 0 := by
  by_cases h_top : p = ∞
  · rw [h_top, eLpNorm_exponent_top, eLpNormEssSup_eq_zero_iff]
  rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_eq_zero_iff (ENNReal.toReal_pos h0 h_top) hf

end ENormedAddMonoid

section MapMeasure

variable {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  {β : Type*} {mβ : MeasurableSpace β} {f : α → β} {g : β → ε}

theorem eLpNormEssSup_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  essSup_map_measure hg.enorm hf

theorem eLpNorm_map_measure (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    exact eLpNormEssSup_map_measure hg hf
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp_zero hp_top,
    lintegral_map' (hg.enorm.pow_const p.toReal) hf, Function.comp_apply]

theorem memLp_map_measure_iff (hg : AEStronglyMeasurable g (Measure.map f μ))
    (hf : AEMeasurable f μ) : MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ := by
  simp [MemLp, eLpNorm_map_measure hg hf, hg.comp_aemeasurable hf, hg]

theorem MemLp.comp_of_map (hg : MemLp g p (Measure.map f μ)) (hf : AEMeasurable f μ) :
    MemLp (g ∘ f) p μ :=
  (memLp_map_measure_iff hg.aestronglyMeasurable hf).1 hg

theorem eLpNorm_comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : AEStronglyMeasurable g ν)
    (hf : MeasurePreserving f μ ν) : eLpNorm (g ∘ f) p μ = eLpNorm g p ν :=
  Eq.symm <| hf.map_eq ▸ eLpNorm_map_measure (hf.map_eq ▸ hg) hf.aemeasurable

theorem AEEqFun.eLpNorm_compMeasurePreserving {ν : MeasureTheory.Measure β} (g : β →ₘ[ν] E)
    (hf : MeasurePreserving f μ ν) :
    eLpNorm (g.compMeasurePreserving f hf) p μ = eLpNorm g p ν := by
  rw [eLpNorm_congr_ae (g.coeFn_compMeasurePreserving _)]
  exact eLpNorm_comp_measurePreserving g.aestronglyMeasurable hf

theorem MemLp.comp_measurePreserving {ν : MeasureTheory.Measure β} (hg : MemLp g p ν)
    (hf : MeasurePreserving f μ ν) : MemLp (g ∘ f) p μ :=
  .comp_of_map (hf.map_eq.symm ▸ hg) hf.aemeasurable

theorem _root_.MeasurableEmbedding.eLpNormEssSup_map_measure (hf : MeasurableEmbedding f) :
    eLpNormEssSup g (Measure.map f μ) = eLpNormEssSup (g ∘ f) μ :=
  hf.essSup_map_measure

theorem _root_.MeasurableEmbedding.eLpNorm_map_measure (hf : MeasurableEmbedding f) :
    eLpNorm g p (Measure.map f μ) = eLpNorm (g ∘ f) p μ := by
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero]
  by_cases hp : p = ∞
  · simp_rw [hp, eLpNorm_exponent_top]
    exact hf.essSup_map_measure
  · simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp_zero hp, hf.lintegral_map, Function.comp_apply]

theorem _root_.MeasurableEmbedding.memLp_map_measure_iff (hf : MeasurableEmbedding f) :
    MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ := by
  simp_rw [MemLp, hf.aestronglyMeasurable_map_iff, hf.eLpNorm_map_measure]

theorem _root_.MeasurableEquiv.memLp_map_measure_iff (f : α ≃ᵐ β) :
    MemLp g p (Measure.map f μ) ↔ MemLp (g ∘ f) p μ :=
  f.measurableEmbedding.memLp_map_measure_iff

end MapMeasure

section Monotonicity

variable {ε ε' : Type*} [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ContinuousENorm ε']

theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) {p : ℝ} (hp : 0 < p) :
    eLpNorm' f p μ ≤ c • eLpNorm' g p μ := by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne.symm, ENNReal.rpow_one, enorm,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top,
    ← ENNReal.coe_mul]
  apply lintegral_mono_ae
  simp_rw [ENNReal.coe_le_coe, ← NNReal.mul_rpow, NNReal.rpow_le_rpow_iff hp]
  exact h

-- TODO: eventually, deprecate and remove the nnnorm version
theorem eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) {p : ℝ} (hp : 0 < p) :
    eLpNorm' f p μ ≤ c • eLpNorm' g p μ := by
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← ENNReal.coe_rpow_of_nonneg _ hp.le, ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    have : ¬(p < 0) := by linarith
    simp [ENNReal.mul_rpow_eq_ite, this]
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]

/-- If `‖f x‖ₑ ≤ c * ‖g x‖ₑ` a.e., `eLpNorm' f p μ ≤ c * eLpNorm' g p μ` for all `p ∈ (0, ∞)`. -/
theorem eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul {f : α → ε} {c : ℝ≥0∞} {g : α → ε'} {p : ℝ}
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (hp : 0 < p) :
    eLpNorm' f p μ ≤ c * eLpNorm' g p μ := by
  have hp' : ¬(p < 0) := by linarith
  by_cases hc : c = ⊤
  · by_cases hg' : eLpNorm' g p μ = 0
    · have : ∀ᵐ (x : α) ∂μ, ‖g x‖ₑ = 0 := by
        simp only [eLpNorm'_eq_lintegral_enorm, one_div, ENNReal.rpow_eq_zero_iff, inv_pos, hp,
          and_true, inv_neg'', hp', and_false, or_false] at hg'
        rw [MeasureTheory.lintegral_eq_zero_iff' (by fun_prop)] at hg'
        exact hg'.mono fun x hx ↦ by simpa [hp, hp'] using hx
      have : ∀ᵐ (x : α) ∂μ, ‖f x‖ₑ = 0 := (this.and h).mono fun x ⟨h, h'⟩ ↦ by simp_all
      simpa only [hg', mul_zero, nonpos_iff_eq_zero] using eLpNorm'_eq_zero_of_ae_eq_zero hp this
    · simp_all
  have : c ^ p ≠ ⊤ := by simp [hp.le, hc]
  simp_rw [eLpNorm'_eq_lintegral_enorm]
  rw [← ENNReal.rpow_le_rpow_iff hp, ENNReal.mul_rpow_of_nonneg _ _ hp.le]
  simp_rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one,
    ← lintegral_const_mul' _ _ this]
  apply lintegral_mono_ae
  have aux (x) : (↑c) ^ p * ‖g x‖ₑ ^ p = (↑c * ‖g x‖ₑ) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, hp']
  simpa [ENNReal.coe_rpow_of_nonneg _ hp.le, aux, ENNReal.rpow_le_rpow_iff hp]

end ESeminormedAddMonoid

-- TODO: eventually, deprecate and remove the nnnorm version
theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0∞}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : eLpNormEssSup f μ ≤ c • eLpNormEssSup g μ :=
  calc
    essSup (‖f ·‖ₑ) μ ≤ essSup (c * ‖g ·‖ₑ) μ := essSup_mono_ae <| h
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

theorem eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : eLpNormEssSup f μ ≤ c • eLpNormEssSup g μ :=
  calc
    essSup (‖f ·‖ₑ) μ ≤ essSup (fun x => (↑(c * ‖g x‖₊) : ℝ≥0∞)) μ :=
      essSup_mono_ae <| h.mono fun _ hx => ENNReal.coe_le_coe.mpr hx
    _ = essSup (c * ‖g ·‖ₑ) μ := by simp_rw [ENNReal.coe_mul, enorm]
    _ = c • essSup (‖g ·‖ₑ) μ := ENNReal.essSup_const_mul

-- TODO: eventually, deprecate and remove the nnnorm version
theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (p : ℝ≥0∞) : eLpNorm f p μ ≤ c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul' h (ENNReal.toReal_pos h0 h_top)

theorem eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) (p : ℝ≥0∞) : eLpNorm f p μ ≤ c • eLpNorm g p μ := by
  by_cases h0 : p = 0
  · simp [h0]
  by_cases h_top : p = ∞
  · rw [h_top]
    exact eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul h
  simp_rw [eLpNorm_eq_eLpNorm' h0 h_top]
  exact eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul h (ENNReal.toReal_pos h0 h_top)

-- TODO: add the whole family of lemmas?
private theorem le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg {α}
    [Semiring α] [LinearOrder α] [IsStrictOrderedRing α]
    {a b c : α} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) : a ≤ b * c ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]

/-- When `c` is negative, `‖f x‖ ≤ c * ‖g x‖` is nonsense and forces both `f` and `g` to have an
`eLpNorm` of `0`. -/
theorem eLpNorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
    eLpNorm f p μ = 0 ∧ eLpNorm g p μ = 0 := by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [eLpNorm_congr_ae h.1, eLpNorm_congr_ae h.2]

theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) :
    eLpNorm f p μ ≤ ENNReal.ofReal c * eLpNorm g p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _

-- TODO: eventually, deprecate and remove the nnnorm version
/-- If `‖f x‖ₑ ≤ c * ‖g x‖ₑ`, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`.

This version assumes `c` is finite, but requires no measurability hypothesis on `g`. -/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0}
    (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) (p : ℝ≥0∞) :
    eLpNorm f p μ ≤ c * eLpNorm g p μ := by
  apply eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' h

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] in
/-- If `‖f x‖ₑ ≤ c * ‖g x‖ₑ`, then `eLpNorm f p μ ≤ c * eLpNorm g p μ`.

This version allows `c = ∞`, but requires `g` to be a.e. strongly measurable. -/
theorem eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' {f : α → ε} {c : ℝ≥0∞} {g : α → ε'} (p : ℝ≥0∞)
    (hg : AEStronglyMeasurable g μ) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) :
    eLpNorm f p μ ≤ c * eLpNorm g p μ := by
  by_cases h₀ : p = 0
  · simp [h₀]
  simp only [eLpNorm, h₀, ↓reduceIte, mul_ite]
  by_cases hp' : p = ⊤
  · simpa [hp'] using eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul' h
  · simpa [hp'] using eLpNorm'_le_mul_eLpNorm'_of_ae_le_mul hg h (ENNReal.toReal_pos h₀ hp')

theorem MemLp.of_nnnorm_le_mul {f : α → E} {g : α → F} {c : ℝ≥0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : MemLp f p μ :=
  ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top hg.eLpNorm_lt_top⟩

theorem MemLp.of_enorm_le_mul
    {f : α → ε} {g : α → ε'} {c : ℝ≥0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul' hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top hg.eLpNorm_lt_top⟩

theorem MemLp.of_le_mul {f : α → E} {g : α → F} {c : ℝ} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : MemLp f p μ :=
  ⟨hf,
    (eLpNorm_le_mul_eLpNorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hg.eLpNorm_lt_top⟩

-- TODO: eventually, deprecate and remove the nnnorm version
theorem MemLp.of_le_mul' {f : α → ε} {g : α → ε'} {c : ℝ≥0} (hg : MemLp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ c * ‖g x‖ₑ) : MemLp f p μ :=
  ⟨hf, (eLpNorm_le_mul_eLpNorm_of_ae_le_mul' hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_lt_top hg.eLpNorm_lt_top⟩

end Monotonicity

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {c : 𝕜} {f : α → F}

theorem eLpNorm'_const_smul_le (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul (Eventually.of_forall fun _ => nnnorm_smul_le ..) hq

theorem eLpNormEssSup_const_smul_le : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le])

theorem eLpNorm_const_smul_le : eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul
    (Eventually.of_forall fun _ => by simp [nnnorm_smul_le]) _

theorem MemLp.const_smul (hf : MemLp f p μ) (c : 𝕜) : MemLp (c • f) p μ :=
  ⟨hf.1.const_smul c, eLpNorm_const_smul_le.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

theorem MemLp.const_mul {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

theorem MemLp.mul_const {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (fun x => f x * c) p μ :=
  hf.const_smul (MulOpposite.op c)

end IsBoundedSMul

section ENormSMulClass

variable {𝕜 : Type*} [NormedRing 𝕜]
  {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] [SMul 𝕜 ε] [ENormSMulClass 𝕜 ε]
  {c : 𝕜} {f : α → ε}

theorem eLpNorm'_const_smul_le' (hq : 0 < q) : eLpNorm' (c • f) q μ ≤ ‖c‖ₑ * eLpNorm' f q μ :=
  eLpNorm'_le_nnreal_smul_eLpNorm'_of_ae_le_mul'
    (Eventually.of_forall fun _ ↦ le_of_eq (enorm_smul ..)) hq

theorem eLpNormEssSup_const_smul_le' : eLpNormEssSup (c • f) μ ≤ ‖c‖ₑ * eLpNormEssSup f μ :=
  eLpNormEssSup_le_nnreal_smul_eLpNormEssSup_of_ae_le_mul'
    (Eventually.of_forall fun _ => by simp [enorm_smul])

theorem eLpNorm_const_smul_le' : eLpNorm (c • f) p μ ≤ ‖c‖ₑ * eLpNorm f p μ :=
  eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (Eventually.of_forall fun _ => le_of_eq (enorm_smul ..)) _

theorem MemLp.const_smul' [ContinuousConstSMul 𝕜 ε] (hf : MemLp f p μ) (c : 𝕜) :
    MemLp (c • f) p μ :=
  ⟨hf.1.const_smul c, eLpNorm_const_smul_le'.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hf.2)⟩

theorem MemLp.const_mul' {f : α → 𝕜} (hf : MemLp f p μ) (c : 𝕜) : MemLp (fun x => c * f x) p μ :=
  hf.const_smul c

end ENormSMulClass

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.

TODO: do these results hold for any `NormedRing` assuming `NormSMulClass`?
-/

section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]

theorem eLpNorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
    eLpNorm' (c • f) q μ = ‖c‖ₑ * eLpNorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [eLpNorm'_eq_lintegral_enorm, hq_pos]
  refine le_antisymm (eLpNorm'_const_smul_le hq_pos) <| ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm'_const_smul_le (c := c⁻¹) (f := c • f) hq_pos

theorem eLpNormEssSup_const_smul (c : 𝕜) (f : α → F) :
    eLpNormEssSup (c • f) μ = ‖c‖ₑ * eLpNormEssSup f μ := by
  simp_rw [eLpNormEssSup_eq_essSup_enorm, Pi.smul_apply, enorm_smul,
    ENNReal.essSup_const_mul]

theorem eLpNorm_const_smul (c : 𝕜) (f : α → F) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (c • f) p μ = ‖c‖ₑ * eLpNorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm eLpNorm_const_smul_le <| ENNReal.mul_le_of_le_div' ?_
  simpa [enorm_inv, hc, ENNReal.div_eq_inv_mul]
    using eLpNorm_const_smul_le (c := c⁻¹) (f := c • f)

lemma eLpNorm_nsmul [NormedSpace ℝ F] (n : ℕ) (f : α → F) :
    eLpNorm (n • f) p μ = n * eLpNorm f p μ := by
  simpa [Nat.cast_smul_eq_nsmul] using eLpNorm_const_smul (n : ℝ) f ..

end NormedSpace

theorem le_eLpNorm_of_bddBelow (hp : p ≠ 0) (hp' : p ≠ ∞) {f : α → F} (C : ℝ≥0) {s : Set α}
    (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖f x‖₊) :
    C • μ s ^ (1 / p.toReal) ≤ eLpNorm f p μ := by
  rw [ENNReal.smul_def, smul_eq_mul, eLpNorm_eq_lintegral_rpow_enorm hp hp',
    one_div, ENNReal.le_rpow_inv_iff (ENNReal.toReal_pos hp hp'),
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ (ENNReal.toReal_pos hp hp').ne.symm, ENNReal.rpow_one, ← setLIntegral_const,
    ← lintegral_indicator hs]
  refine lintegral_mono_ae ?_
  filter_upwards [hf] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem, hxs, true_implies] at hx ⊢
    gcongr
    rwa [coe_le_enorm]
  · simp [Set.indicator_of_notMem hxs]

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜] {f : α → 𝕜}

@[simp] lemma eLpNorm_conj (f : α → 𝕜) (p : ℝ≥0∞) (μ : Measure α) :
    eLpNorm (conj f) p μ = eLpNorm f p μ := by simp [← eLpNorm_norm]

theorem MemLp.re (hf : MemLp f p μ) : MemLp (fun x => RCLike.re (f x)) p μ := by
  have : ∀ x, ‖RCLike.re (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_re_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_re.comp_aestronglyMeasurable hf.1

theorem MemLp.im (hf : MemLp f p μ) : MemLp (fun x => RCLike.im (f x)) p μ := by
  have : ∀ x, ‖RCLike.im (f x)‖ ≤ 1 * ‖f x‖ := by
    intro x
    rw [one_mul]
    exact RCLike.norm_im_le_norm (f x)
  refine hf.of_le_mul ?_ (Eventually.of_forall this)
  exact RCLike.continuous_im.comp_aestronglyMeasurable hf.1

end RCLike

section Liminf

variable [MeasurableSpace E] [OpensMeasurableSpace E] {R : ℝ≥0}

theorem ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd {p : ℝ≥0∞} {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => ((‖f n x‖ₑ) ^ p.toReal : ℝ≥0∞)) atTop < ∞ := by
  by_cases hp0 : p.toReal = 0
  · simp only [hp0, ENNReal.rpow_zero]
    filter_upwards with _
    rw [liminf_const (1 : ℝ≥0∞)]
    exact ENNReal.one_lt_top
  have hp : p ≠ 0 := fun h => by simp [h] at hp0
  have hp' : p ≠ ∞ := fun h => by simp [h] at hp0
  refine
    ae_lt_top (.liminf fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
      (lt_of_le_of_lt
          (lintegral_liminf_le fun n => (hfmeas n).nnnorm.coe_nnreal_ennreal.pow_const p.toReal)
          (lt_of_le_of_lt ?_ (by finiteness : (R : ℝ≥0∞) ^ p.toReal < ∞))).ne
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm hp hp', one_div] at hbdd
  simp_rw [liminf_eq, eventually_atTop]
  exact
    sSup_le fun b ⟨a, ha⟩ =>
      (ha a le_rfl).trans ((ENNReal.rpow_inv_le_iff (ENNReal.toReal_pos hp hp')).1 (hbdd _))

theorem ae_bdd_liminf_atTop_of_eLpNorm_bdd {p : ℝ≥0∞} (hp : p ≠ 0) {f : ℕ → α → E}
    (hfmeas : ∀ n, Measurable (f n)) (hbdd : ∀ n, eLpNorm (f n) p μ ≤ R) :
    ∀ᵐ x ∂μ, liminf (fun n => (‖f n x‖ₑ)) atTop < ∞ := by
  by_cases hp' : p = ∞
  · subst hp'
    simp_rw [eLpNorm_exponent_top] at hbdd
    have : ∀ n, ∀ᵐ x ∂μ, (‖f n x‖ₑ) < R + 1 := fun n =>
      ae_lt_of_essSup_lt
        (lt_of_le_of_lt (hbdd n) <| ENNReal.lt_add_right ENNReal.coe_ne_top one_ne_zero)
    rw [← ae_all_iff] at this
    filter_upwards [this] with x hx using lt_of_le_of_lt
        (liminf_le_of_frequently_le' <| Frequently.of_forall fun n => (hx n).le)
        (ENNReal.add_lt_top.2 ⟨ENNReal.coe_lt_top, ENNReal.one_lt_top⟩)
  filter_upwards [ae_bdd_liminf_atTop_rpow_of_eLpNorm_bdd hfmeas hbdd] with x hx
  have hppos : 0 < p.toReal := ENNReal.toReal_pos hp hp'
  have :
    liminf (fun n => (‖f n x‖ₑ) ^ p.toReal) atTop =
      liminf (fun n => (‖f n x‖ₑ)) atTop ^ p.toReal := by
    change
      liminf (fun n => ENNReal.orderIsoRpow p.toReal hppos (‖f n x‖ₑ)) atTop =
        ENNReal.orderIsoRpow p.toReal hppos (liminf (fun n => (‖f n x‖ₑ)) atTop)
    refine (OrderIso.liminf_apply (ENNReal.orderIsoRpow p.toReal _) ?_ ?_ ?_ ?_).symm <;>
      isBoundedDefault
  rw [this] at hx
  rw [← ENNReal.rpow_one (liminf (‖f · x‖ₑ) atTop), ← mul_inv_cancel₀ hppos.ne.symm,
    ENNReal.rpow_mul]
  exact ENNReal.rpow_lt_top_of_nonneg (inv_nonneg.2 hppos.le) hx.ne

end Liminf

/-- A continuous function with compact support belongs to `L^∞`.
See `Continuous.memLp_of_hasCompactSupport` for a version for `L^p`. -/
theorem _root_.Continuous.memLp_top_of_hasCompactSupport
    {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {f : X → E} (hf : Continuous f) (h'f : HasCompactSupport f) (μ : Measure X) : MemLp f ⊤ μ := by
  borelize E
  rcases hf.bounded_above_of_compact_support h'f with ⟨C, hC⟩
  apply memLp_top_of_bound ?_ C (Filter.Eventually.of_forall hC)
  exact (hf.stronglyMeasurable_of_hasCompactSupport h'f).aestronglyMeasurable

section UnifTight

/-- A single function that is `MemLp f p μ` is tight with respect to `μ`. -/
theorem MemLp.exists_eLpNorm_indicator_compl_lt {β : Type*} [NormedAddCommGroup β] (hp_top : p ≠ ∞)
    {f : α → β} (hf : MemLp f p μ) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ s : Set α, MeasurableSet s ∧ μ s < ∞ ∧ eLpNorm (sᶜ.indicator f) p μ < ε := by
  rcases eq_or_ne p 0 with rfl | hp₀
  · use ∅; simp [pos_iff_ne_zero.2 hε] -- first take care of `p = 0`
  · obtain ⟨s, hsm, hs, hε⟩ :
        ∃ s, MeasurableSet s ∧ μ s < ∞ ∧ ∫⁻ a in sᶜ, (‖f a‖ₑ) ^ p.toReal ∂μ < ε ^ p.toReal := by
      apply exists_setLIntegral_compl_lt
      · exact ((eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp₀ hp_top).1 hf.2).ne
      · simp [*]
    refine ⟨s, hsm, hs, ?_⟩
    rwa [eLpNorm_indicator_eq_eLpNorm_restrict hsm.compl,
      eLpNorm_eq_lintegral_rpow_enorm hp₀ hp_top, one_div, ENNReal.rpow_inv_lt_iff]
    simp [ENNReal.toReal_pos, *]

end UnifTight
end Lp
end MeasureTheory

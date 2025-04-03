/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Eric Wieser
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Compare Lp seminorms for different values of `p`

In this file we compare `MeasureTheory.eLpNorm'` and `MeasureTheory.eLpNorm` for different
exponents.
-/

open Filter
open scoped ENNReal Topology

namespace MeasureTheory

section SameSpace

variable {α E : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E] {μ : Measure α} {f : α → E}

theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ ≤ eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : ℝ≥0∞)
  have h_rw : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) = ∫⁻ a, ((‖f a‖₊ : ℝ≥0∞) * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp [g]
  repeat' rw [eLpNorm'_eq_lintegral_nnnorm]
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by field_simp [r, hp0_lt.ne', hq0_lt.ne']
  calc
    (∫⁻ a : α, (↑‖f a‖₊ * g a) ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm aemeasurable_const
    _ = (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp [r, g]

@[deprecated (since := "2024-07-27")]
alias snorm'_le_snorm'_mul_rpow_measure_univ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ

theorem eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ {q : ℝ} (hq_pos : 0 < q) :
    eLpNorm' f q μ ≤ eLpNormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) ≤ ∫⁻ _ : α, eLpNormEssSup f μ ^ q ∂μ := by
    refine lintegral_mono_ae ?_
    have h_nnnorm_le_eLpNorm_ess_sup := coe_nnnorm_ae_le_eLpNormEssSup f μ
    exact h_nnnorm_le_eLpNorm_ess_sup.mono fun x hx => by gcongr
  rw [eLpNorm', ← ENNReal.rpow_one (eLpNormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel₀ (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul, one_div, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)]
  gcongr
  rwa [lintegral_const] at h_le

@[deprecated (since := "2024-07-27")]
alias snorm'_le_snormEssSup_mul_rpow_measure_univ := eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ

theorem eLpNorm_le_eLpNorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ eLpNorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  by_cases hp0 : p = 0
  · simp [hp0, zero_le]
  rw [← Ne] at hp0
  have hp0_lt : 0 < p := lt_of_le_of_ne (zero_le _) hp0.symm
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hq_top : q = ∞
  · simp only [hq_top, _root_.div_zero, one_div, ENNReal.top_toReal, sub_zero, eLpNorm_exponent_top,
      GroupWithZero.inv_zero]
    by_cases hp_top : p = ∞
    · simp only [hp_top, ENNReal.rpow_zero, mul_one, ENNReal.top_toReal, sub_zero,
        GroupWithZero.inv_zero, eLpNorm_exponent_top]
      exact le_rfl
    rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0_lt.ne' hp_top
    refine (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos).trans (le_of_eq ?_)
    congr
    exact one_div _
  have hp_lt_top : p < ∞ := hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0_lt.ne' hp_lt_top.ne
  rw [eLpNorm_eq_eLpNorm' hp0_lt.ne.symm hp_lt_top.ne, eLpNorm_eq_eLpNorm' hq0_lt.ne.symm hq_top]
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  exact eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq_real hf

@[deprecated (since := "2024-07-27")]
alias snorm_le_snorm_mul_rpow_measure_univ := eLpNorm_le_eLpNorm_mul_rpow_measure_univ

theorem eLpNorm'_le_eLpNorm'_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ ≤ eLpNorm' f q μ := by
  have h_le_μ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ

@[deprecated (since := "2024-07-27")]
alias snorm'_le_snorm'_of_exponent_le := eLpNorm'_le_eLpNorm'_of_exponent_le

theorem eLpNorm'_le_eLpNormEssSup {q : ℝ} (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' f q μ ≤ eLpNormEssSup f μ :=
  (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hq_pos).trans_eq (by simp [measure_univ])

@[deprecated (since := "2024-07-27")]
alias snorm'_le_snormEssSup := eLpNorm'_le_eLpNormEssSup

theorem eLpNorm_le_eLpNorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) : eLpNorm f p μ ≤ eLpNorm f q μ :=
  (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))

@[deprecated (since := "2024-07-27")]
alias snorm_le_snorm_of_exponent_le := eLpNorm_le_eLpNorm_of_exponent_le

theorem eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le {p q : ℝ} [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : eLpNorm' f q μ < ∞) (hp_nonneg : 0 ≤ p)
    (hpq : p ≤ q) : eLpNorm' f p μ < ∞ := by
  rcases le_or_lt p 0 with hp_nonpos | hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    eLpNorm' f p μ ≤ eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      refine Or.inl ⟨hfq_lt_top, ENNReal.rpow_lt_top_of_nonneg ?_ (measure_ne_top μ Set.univ)⟩
      rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv₀ hq_pos hp_pos]

@[deprecated (since := "2024-07-27")]
alias snorm'_lt_top_of_snorm'_lt_top_of_exponent_le :=
  eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le

theorem Memℒp.memℒp_of_exponent_le {p q : ℝ≥0∞} [IsFiniteMeasure μ] {f : α → E} (hfq : Memℒp f q μ)
    (hpq : p ≤ q) : Memℒp f p μ := by
  cases' hfq with hfq_m hfq_lt_top
  by_cases hp0 : p = 0
  · rwa [hp0, memℒp_zero_iff_aestronglyMeasurable]
  rw [← Ne] at hp0
  refine ⟨hfq_m, ?_⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  by_cases hq_top : q = ∞
  · rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    rw [hq_top, eLpNorm_exponent_top] at hfq_lt_top
    refine lt_of_le_of_lt (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos) ?_
    refine ENNReal.mul_lt_top hfq_lt_top ?_
    exact ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (measure_ne_top μ Set.univ)
  have hq0 : q ≠ 0 := by
    by_contra hq_eq_zero
    have hp_eq_zero : p = 0 := le_antisymm (by rwa [hq_eq_zero] at hpq) (zero_le _)
    rw [hp_eq_zero, ENNReal.zero_toReal] at hp_pos
    exact (lt_irrefl _) hp_pos
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  rw [eLpNorm_eq_eLpNorm' hq0 hq_top] at hfq_lt_top
  exact eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le hfq_m hfq_lt_top hp_pos.le hpq_real

end SameSpace

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {μ : Measure α}
  {f : α → E} {g : α → F}

theorem eLpNorm_le_eLpNorm_top_mul_eLpNorm (p : ℝ≥0∞) (f : α → E) {g : α → F}
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm f ∞ μ * eLpNorm g p μ := by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, eLpNorm_exponent_top]
    refine le_trans (essSup_mono_ae <| h.mono fun a ha => ?_) (ENNReal.essSup_mul_le _ _)
    simp_rw [Pi.mul_apply, enorm_eq_nnnorm, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact ha
  by_cases hp_zero : p = 0
  · simp only [hp_zero, eLpNorm_exponent_zero, mul_zero, le_zero_iff]
  simp_rw [eLpNorm_eq_lintegral_rpow_nnnorm hp_zero hp_top, eLpNorm_exponent_top, eLpNormEssSup]
  calc
    (∫⁻ x, (‖b (f x) (g x)‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤
        (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal * (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      gcongr ?_ ^ _
      refine lintegral_mono_ae (h.mono fun a ha => ?_)
      rw [← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
      refine ENNReal.rpow_le_rpow ?_ ENNReal.toReal_nonneg
      rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
      exact ha
    _ ≤
        (∫⁻ x, essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ ^ p.toReal * (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^
          (1 / p.toReal) := by
      gcongr ?_ ^ _
      refine lintegral_mono_ae ?_
      filter_upwards [@ENNReal.ae_le_essSup _ _ μ fun x => (‖f x‖₊ : ℝ≥0∞)] with x hx
      gcongr
    _ = essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ *
        (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      rw [lintegral_const_mul'']
      swap; · exact hg.nnnorm.aemeasurable.coe_nnreal_ennreal.pow aemeasurable_const
      rw [ENNReal.mul_rpow_of_nonneg]
      swap
      · rw [one_div_nonneg]
        exact ENNReal.toReal_nonneg
      rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel₀, ENNReal.rpow_one]
      rw [Ne, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hp_zero, hp_top⟩

@[deprecated (since := "2024-07-27")]
alias snorm_le_snorm_top_mul_snorm := eLpNorm_le_eLpNorm_top_mul_eLpNorm

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → F) (b : E → F → G) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm f p μ * eLpNorm g ∞ μ :=
  calc
    eLpNorm (fun x ↦ b (f x) (g x)) p μ ≤ eLpNorm g ∞ μ * eLpNorm f p μ :=
      eLpNorm_le_eLpNorm_top_mul_eLpNorm p g hf (flip b) <| by simpa only [mul_comm] using h
    _ = eLpNorm f p μ * eLpNorm g ∞ μ := mul_comm _ _

@[deprecated (since := "2024-07-27")]
alias snorm_le_snorm_mul_snorm_top := eLpNorm_le_eLpNorm_mul_eLpNorm_top

theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm' {p q r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) :
    eLpNorm' (fun x => b (f x) (g x)) p μ ≤ eLpNorm' f q μ * eLpNorm' g r μ := by
  rw [eLpNorm']
  calc
    (∫⁻ a : α, ↑‖b (f a) (g a)‖₊ ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑(‖f a‖₊ * ‖g a‖₊) ^ p ∂μ) ^ (1 / p) :=
      (ENNReal.rpow_le_rpow_iff <| one_div_pos.mpr hp0_lt).mpr <|
        lintegral_mono_ae <|
          h.mono fun a ha => (ENNReal.rpow_le_rpow_iff hp0_lt).mpr <| ENNReal.coe_le_coe.mpr <| ha
    _ ≤ _ := ?_
  simp_rw [eLpNorm', ENNReal.coe_mul]
  exact ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm hg.ennnorm

@[deprecated (since := "2024-07-27")]
alias snorm'_le_snorm'_mul_snorm' := eLpNorm'_le_eLpNorm'_mul_eLpNorm'

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm {p q r : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) (hpqr : 1 / p = 1 / q + 1 / r) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm f q μ * eLpNorm g r μ := by
  by_cases hp_zero : p = 0
  · simp [hp_zero]
  have hq_ne_zero : q ≠ 0 := by
    intro hq_zero
    simp only [hq_zero, hp_zero, one_div, ENNReal.inv_zero, top_add, ENNReal.inv_eq_top] at hpqr
  have hr_ne_zero : r ≠ 0 := by
    intro hr_zero
    simp only [hr_zero, hp_zero, one_div, ENNReal.inv_zero, add_top, ENNReal.inv_eq_top] at hpqr
  by_cases hq_top : q = ∞
  · have hpr : p = r := by
      simpa only [hq_top, one_div, ENNReal.inv_top, zero_add, inv_inj] using hpqr
    rw [← hpr, hq_top]
    exact eLpNorm_le_eLpNorm_top_mul_eLpNorm p f hg b h
  by_cases hr_top : r = ∞
  · have hpq : p = q := by
      simpa only [hr_top, one_div, ENNReal.inv_top, add_zero, inv_inj] using hpqr
    rw [← hpq, hr_top]
    exact eLpNorm_le_eLpNorm_mul_eLpNorm_top p hf g b h
  have hpq : p < q := by
    suffices 1 / q < 1 / p by rwa [one_div, one_div, ENNReal.inv_lt_inv] at this
    rw [hpqr]
    refine ENNReal.lt_add_right ?_ ?_
    · simp only [hq_ne_zero, one_div, Ne, ENNReal.inv_eq_top, not_false_iff]
    · simp only [hr_top, one_div, Ne, ENNReal.inv_eq_zero, not_false_iff]
  rw [eLpNorm_eq_eLpNorm' hp_zero (hpq.trans_le le_top).ne, eLpNorm_eq_eLpNorm' hq_ne_zero hq_top,
    eLpNorm_eq_eLpNorm' hr_ne_zero hr_top]
  refine eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf hg _ h ?_ ?_ ?_
  · exact ENNReal.toReal_pos hp_zero (hpq.trans_le le_top).ne
  · exact ENNReal.toReal_strict_mono hq_top hpq
  rw [← ENNReal.one_toReal, ← ENNReal.toReal_div, ← ENNReal.toReal_div, ← ENNReal.toReal_div, hpqr,
    ENNReal.toReal_add]
  · simp only [hq_ne_zero, one_div, Ne, ENNReal.inv_eq_top, not_false_iff]
  · simp only [hr_ne_zero, one_div, Ne, ENNReal.inv_eq_top, not_false_iff]

@[deprecated (since := "2024-07-27")]
alias snorm_le_snorm_mul_snorm_of_nnnorm := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm {p q r : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖) (hpqr : 1 / p = 1 / q + 1 / r) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm f q μ * eLpNorm g r μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg b h hpqr

@[deprecated (since := "2024-07-27")]
alias snorm_le_snorm_mul_snorm'_of_norm := eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm

end Bilinear

section BoundedSMul

variable {𝕜 α E F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]
  [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [BoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [MulActionWithZero 𝕜 F] [BoundedSMul 𝕜 F] {f : α → E}

theorem eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p : ℝ≥0∞) (hf : AEStronglyMeasurable f μ)
    (φ : α → 𝕜) : eLpNorm (φ • f) p μ ≤ eLpNorm φ ∞ μ * eLpNorm f p μ :=
  (eLpNorm_le_eLpNorm_top_mul_eLpNorm p φ hf (· • ·)
    (Eventually.of_forall fun _ => nnnorm_smul_le _ _) : _)

@[deprecated (since := "2024-07-27")]
alias snorm_smul_le_snorm_top_mul_snorm := eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm

theorem eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) (f : α → E) {φ : α → 𝕜}
    (hφ : AEStronglyMeasurable φ μ) : eLpNorm (φ • f) p μ ≤ eLpNorm φ p μ * eLpNorm f ∞ μ :=
  (eLpNorm_le_eLpNorm_mul_eLpNorm_top p hφ f (· • ·)
    (Eventually.of_forall fun _ => nnnorm_smul_le _ _) : _)

@[deprecated (since := "2024-07-27")]
alias snorm_smul_le_snorm_mul_snorm_top := eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top

theorem eLpNorm'_smul_le_mul_eLpNorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : eLpNorm' (φ • f) p μ ≤ eLpNorm' φ q μ * eLpNorm' f r μ :=
  eLpNorm'_le_eLpNorm'_mul_eLpNorm' hφ hf (· • ·) (Eventually.of_forall fun _ => nnnorm_smul_le _ _)
    hp0_lt hpq hpqr

@[deprecated (since := "2024-07-27")]
alias snorm'_smul_le_mul_snorm' := eLpNorm'_smul_le_mul_eLpNorm'

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
theorem eLpNorm_smul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    eLpNorm (φ • f) p μ ≤ eLpNorm φ q μ * eLpNorm f r μ :=
  (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hφ hf (· • ·)
      (Eventually.of_forall fun _ => nnnorm_smul_le _ _) hpqr :
    _)

@[deprecated (since := "2024-07-27")]
alias snorm_smul_le_mul_snorm := eLpNorm_smul_le_mul_eLpNorm

theorem Memℒp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f r μ) (hφ : Memℒp φ q μ)
    (hpqr : 1 / p = 1 / q + 1 / r) : Memℒp (φ • f) p μ :=
  ⟨hφ.1.smul hf.1,
    (eLpNorm_smul_le_mul_eLpNorm hf.1 hφ.1 hpqr).trans_lt
      (ENNReal.mul_lt_top hφ.eLpNorm_lt_top hf.eLpNorm_lt_top)⟩

theorem Memℒp.smul_of_top_right {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f p μ)
    (hφ : Memℒp φ ∞ μ) : Memℒp (φ • f) p μ := by
  apply hf.smul hφ
  simp only [ENNReal.div_top, zero_add]

theorem Memℒp.smul_of_top_left {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f ∞ μ)
    (hφ : Memℒp φ p μ) : Memℒp (φ • f) p μ := by
  apply hf.smul hφ
  simp only [ENNReal.div_top, add_zero]

end BoundedSMul

section Mul

variable {α : Type*} [MeasurableSpace α] {𝕜 : Type*} [NormedRing 𝕜] {μ : Measure α}
  {p q r : ℝ≥0∞} {f : α → 𝕜} {φ : α → 𝕜}

theorem Memℒp.mul (hf : Memℒp f r μ) (hφ : Memℒp φ q μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    Memℒp (φ * f) p μ :=
  Memℒp.smul hf hφ hpqr

/-- Variant of `Memℒp.mul` where the function is written as `fun x ↦ φ x * f x`
instead of `φ * f`. -/
theorem Memℒp.mul' (hf : Memℒp f r μ) (hφ : Memℒp φ q μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    Memℒp (fun x ↦ φ x * f x) p μ :=
  Memℒp.smul hf hφ hpqr

theorem Memℒp.mul_of_top_right (hf : Memℒp f p μ) (hφ : Memℒp φ ∞ μ) : Memℒp (φ * f) p μ :=
  Memℒp.smul_of_top_right hf hφ

/-- Variant of `Memℒp.mul_of_top_right` where the function is written as `fun x ↦ φ x * f x`
instead of `φ * f`. -/
theorem Memℒp.mul_of_top_right' (hf : Memℒp f p μ) (hφ : Memℒp φ ∞ μ) :
    Memℒp (fun x ↦ φ x * f x) p μ :=
  Memℒp.smul_of_top_right hf hφ

theorem Memℒp.mul_of_top_left (hf : Memℒp f ∞ μ) (hφ : Memℒp φ p μ) : Memℒp (φ * f) p μ :=
  Memℒp.smul_of_top_left hf hφ

/-- Variant of `Memℒp.mul_of_top_left` where the function is written as `fun x ↦ φ x * f x`
instead of `φ * f`. -/
theorem Memℒp.mul_of_top_left' (hf : Memℒp f ∞ μ) (hφ : Memℒp φ p μ) :
    Memℒp (fun x ↦ φ x * f x) p μ :=
  Memℒp.smul_of_top_left hf hφ

end Mul

end MeasureTheory

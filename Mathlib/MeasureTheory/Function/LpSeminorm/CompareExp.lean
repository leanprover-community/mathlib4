/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Sébastien Gouëzel, Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Compare `ℒᵖ` seminorms with different `p`s
-/

theorem snorm'_norm_rpow (f : α → F) (p q : ℝ) (hq_pos : 0 < q) :
    snorm' (fun x => ‖f x‖ ^ q) p μ = snorm' f (p * q) μ ^ q := by
  simp_rw [snorm']
  rw [← ENNReal.rpow_mul, ← one_div_mul_one_div]
  simp_rw [one_div]
  rw [mul_assoc, inv_mul_cancel hq_pos.ne.symm, mul_one]
  congr
  ext1 x
  simp_rw [← ofReal_norm_eq_coe_nnnorm]
  rw [Real.norm_eq_abs, abs_eq_self.mpr (Real.rpow_nonneg_of_nonneg (norm_nonneg _) _), mul_comm, ←
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hq_pos.le, ENNReal.rpow_mul]
#align measure_theory.snorm'_norm_rpow MeasureTheory.snorm'_norm_rpow

theorem snorm_norm_rpow (f : α → F) (hq_pos : 0 < q) :
    snorm (fun x => ‖f x‖ ^ q) p μ = snorm f (p * ENNReal.ofReal q) μ ^ q := by
  by_cases h0 : p = 0
  · simp [h0, ENNReal.zero_rpow_of_pos hq_pos]
  by_cases hp_top : p = ∞
  · simp only [hp_top, snorm_exponent_top, ENNReal.top_mul', hq_pos.not_le, ENNReal.ofReal_eq_zero,
      if_false, snorm_exponent_top, snormEssSup]
    have h_rpow :
      essSup (fun x : α => (‖‖f x‖ ^ q‖₊ : ℝ≥0∞)) μ =
        essSup (fun x : α => (‖f x‖₊ : ℝ≥0∞) ^ q) μ := by
      congr
      ext1 x
      conv_rhs => rw [← nnnorm_norm]
      rw [ENNReal.coe_rpow_of_nonneg _ hq_pos.le, ENNReal.coe_eq_coe]
      ext
      push_cast
      rw [Real.norm_rpow_of_nonneg (norm_nonneg _)]
    rw [h_rpow]
    have h_rpow_mono := ENNReal.strictMono_rpow_of_pos hq_pos
    have h_rpow_surj := (ENNReal.rpow_left_bijective hq_pos.ne.symm).2
    let iso := h_rpow_mono.orderIsoOfSurjective _ h_rpow_surj
    exact (iso.essSup_apply (fun x => (‖f x‖₊ : ℝ≥0∞)) μ).symm
  rw [snorm_eq_snorm' h0 hp_top, snorm_eq_snorm' _ _]
  swap;
  · refine' mul_ne_zero h0 _
    rwa [Ne.def, ENNReal.ofReal_eq_zero, not_le]
  swap; · exact ENNReal.mul_ne_top hp_top ENNReal.ofReal_ne_top
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hq_pos.le]
  exact snorm'_norm_rpow f p.toReal q hq_pos
#align measure_theory.snorm_norm_rpow MeasureTheory.snorm_norm_rpow

theorem snorm'_le_snorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q) {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    snorm' f p μ ≤ snorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : ℝ≥0∞)
  have h_rw : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) = ∫⁻ a, ((‖f a‖₊ : ℝ≥0∞) * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp [g]
  repeat' rw [snorm']
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by field_simp [r, hp0_lt.ne', hq0_lt.ne']
  calc
    (∫⁻ a : α, (↑‖f a‖₊ * g a) ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm aemeasurable_const
    _ = (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp [r, g]
#align measure_theory.snorm'_le_snorm'_mul_rpow_measure_univ MeasureTheory.snorm'_le_snorm'_mul_rpow_measure_univ

theorem snorm'_le_snormEssSup_mul_rpow_measure_univ (hq_pos : 0 < q) {f : α → F} :
    snorm' f q μ ≤ snormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) ≤ ∫⁻ _ : α, snormEssSup f μ ^ q ∂μ := by
    refine' lintegral_mono_ae _
    have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snormEssSup f μ
    exact h_nnnorm_le_snorm_ess_sup.mono fun x hx => by gcongr
  rw [snorm', ← ENNReal.rpow_one (snormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul, one_div, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)]
  refine' ENNReal.rpow_le_rpow _ (by simp [hq_pos.le])
  rwa [lintegral_const] at h_le
#align measure_theory.snorm'_le_snorm_ess_sup_mul_rpow_measure_univ MeasureTheory.snorm'_le_snormEssSup_mul_rpow_measure_univ

theorem snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q) {f : α → E}
    (hf : AEStronglyMeasurable f μ) :
    snorm f p μ ≤ snorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  by_cases hp0 : p = 0
  · simp [hp0, zero_le]
  rw [← Ne] at hp0
  have hp0_lt : 0 < p := lt_of_le_of_ne (zero_le _) hp0.symm
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hq_top : q = ∞
  · simp only [hq_top, _root_.div_zero, one_div, ENNReal.top_toReal, sub_zero, snorm_exponent_top,
      GroupWithZero.inv_zero]
    by_cases hp_top : p = ∞
    · simp only [hp_top, ENNReal.rpow_zero, mul_one, ENNReal.top_toReal, sub_zero,
        GroupWithZero.inv_zero, snorm_exponent_top]
      exact le_rfl
    rw [snorm_eq_snorm' hp0 hp_top]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0_lt.ne' hp_top
    refine' (snorm'_le_snormEssSup_mul_rpow_measure_univ hp_pos).trans (le_of_eq _)
    congr
    exact one_div _
  have hp_lt_top : p < ∞ := hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0_lt.ne' hp_lt_top.ne
  rw [snorm_eq_snorm' hp0_lt.ne.symm hp_lt_top.ne, snorm_eq_snorm' hq0_lt.ne.symm hq_top]
  have hpq_real : p.toReal ≤ q.toReal := by rwa [ENNReal.toReal_le_toReal hp_lt_top.ne hq_top]
  exact snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq_real hf
#align measure_theory.snorm_le_snorm_mul_rpow_measure_univ MeasureTheory.snorm_le_snorm_mul_rpow_measure_univ

theorem snorm'_le_snorm'_of_exponent_le {m : MeasurableSpace α} {p q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] {f : α → E}
    (hf : AEStronglyMeasurable f μ) : snorm' f p μ ≤ snorm' f q μ := by
  have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ
#align measure_theory.snorm'_le_snorm'_of_exponent_le MeasureTheory.snorm'_le_snorm'_of_exponent_le

theorem snorm'_le_snormEssSup (hq_pos : 0 < q) {f : α → F} [IsProbabilityMeasure μ] :
    snorm' f q μ ≤ snormEssSup f μ :=
  le_trans (snorm'_le_snormEssSup_mul_rpow_measure_univ hq_pos) (le_of_eq (by simp [measure_univ]))
#align measure_theory.snorm'_le_snorm_ess_sup MeasureTheory.snorm'_le_snormEssSup

theorem snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [IsProbabilityMeasure μ]
    {f : α → E} (hf : AEStronglyMeasurable f μ) : snorm f p μ ≤ snorm f q μ :=
  (snorm_le_snorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))
#align measure_theory.snorm_le_snorm_of_exponent_le MeasureTheory.snorm_le_snorm_of_exponent_le

theorem snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [IsFiniteMeasure μ] {f : α → E}
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : snorm' f q μ < ∞) (hp_nonneg : 0 ≤ p)
    (hpq : p ≤ q) : snorm' f p μ < ∞ := by
  cases' le_or_lt p 0 with hp_nonpos hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    snorm' f p μ ≤ snorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      snorm'_le_snorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      refine' Or.inl ⟨hfq_lt_top, ENNReal.rpow_lt_top_of_nonneg _ (measure_ne_top μ Set.univ)⟩
      rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv hq_pos hp_pos]
#align measure_theory.snorm'_lt_top_of_snorm'_lt_top_of_exponent_le MeasureTheory.snorm'_lt_top_of_snorm'_lt_top_of_exponent_le

theorem Memℒp.memℒp_of_exponent_le {p q : ℝ≥0∞} [IsFiniteMeasure μ] {f : α → E} (hfq : Memℒp f q μ)
    (hpq : p ≤ q) : Memℒp f p μ := by
  cases' hfq with hfq_m hfq_lt_top
  by_cases hp0 : p = 0
  · rwa [hp0, memℒp_zero_iff_aestronglyMeasurable]
  rw [← Ne] at hp0
  refine' ⟨hfq_m, _⟩
  by_cases hp_top : p = ∞
  · have hq_top : q = ∞ := by rwa [hp_top, top_le_iff] at hpq
    rw [hp_top]
    rwa [hq_top] at hfq_lt_top
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
  by_cases hq_top : q = ∞
  · rw [snorm_eq_snorm' hp0 hp_top]
    rw [hq_top, snorm_exponent_top] at hfq_lt_top
    refine' lt_of_le_of_lt (snorm'_le_snormEssSup_mul_rpow_measure_univ hp_pos) _
    refine' ENNReal.mul_lt_top hfq_lt_top.ne _
    exact (ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (measure_ne_top μ Set.univ)).ne
  have hq0 : q ≠ 0 := by
    by_contra hq_eq_zero
    have hp_eq_zero : p = 0 := le_antisymm (by rwa [hq_eq_zero] at hpq) (zero_le _)
    rw [hp_eq_zero, ENNReal.zero_toReal] at hp_pos
    exact (lt_irrefl _) hp_pos
  have hpq_real : p.toReal ≤ q.toReal := by rwa [ENNReal.toReal_le_toReal hp_top hq_top]
  rw [snorm_eq_snorm' hp0 hp_top]
  rw [snorm_eq_snorm' hq0 hq_top] at hfq_lt_top
  exact snorm'_lt_top_of_snorm'_lt_top_of_exponent_le hfq_m hfq_lt_top (le_of_lt hp_pos) hpq_real
#align measure_theory.mem_ℒp.mem_ℒp_of_exponent_le MeasureTheory.Memℒp.memℒp_of_exponent_le

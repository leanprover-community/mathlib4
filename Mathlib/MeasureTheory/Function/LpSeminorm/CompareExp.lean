/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Eric Wieser
-/
import Mathlib.MeasureTheory.Function.LpSeminorm
import Mathlib.MeasureTheory.Integral.MeanInequalities

#align_import measure_theory.function.lp_seminorm from "leanprover-community/mathlib"@"c4015acc0a223449d44061e27ddac1835a3852b9"

/-!
# Compare Lp seminorms for different values of `p`

In this file we compare `MeasureTheory.snorm'` and `MeasureTheory.snorm` for different exponents.
-/

open Filter
open scoped ENNReal Topology BigOperators

namespace MeasureTheory

section SameSpace

variable {α E : Type*} {m : MeasurableSpace α} [NormedAddCommGroup E] {μ : Measure α} {f : α → E}

theorem snorm'_le_snorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    snorm' f p μ ≤ snorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : ℝ≥0∞)
  have h_rw : (∫⁻ a, (‖f a‖₊ : ℝ≥0∞) ^ p ∂μ) = ∫⁻ a, ((‖f a‖₊ : ℝ≥0∞) * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp
  repeat' rw [snorm']
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by
    field_simp [(ne_of_lt hp0_lt).symm, (ne_of_lt hq0_lt).symm]
    ring
  calc
    (∫⁻ a : α, (↑‖f a‖₊ * g a) ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm aemeasurable_const
    _ = (∫⁻ a : α, ↑‖f a‖₊ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp
#align measure_theory.snorm'_le_snorm'_mul_rpow_measure_univ MeasureTheory.snorm'_le_snorm'_mul_rpow_measure_univ

theorem snorm'_le_snormEssSup_mul_rpow_measure_univ {q : ℝ} (hq_pos : 0 < q) :
    snorm' f q μ ≤ snormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, (‖f a‖₊ : ℝ≥0∞) ^ q ∂μ) ≤ ∫⁻ _ : α, snormEssSup f μ ^ q ∂μ := by
    refine' lintegral_mono_ae _
    have h_nnnorm_le_snorm_ess_sup := coe_nnnorm_ae_le_snormEssSup f μ
    refine' h_nnnorm_le_snorm_ess_sup.mono fun x hx => by gcongr
  rw [snorm', ← ENNReal.rpow_one (snormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul, one_div, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)]
  gcongr
  rwa [lintegral_const] at h_le
#align measure_theory.snorm'_le_snorm_ess_sup_mul_rpow_measure_univ MeasureTheory.snorm'_le_snormEssSup_mul_rpow_measure_univ

theorem snorm_le_snorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    snorm f p μ ≤ snorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  by_cases hp0 : p = 0
  · simp [hp0, zero_le]
  rw [← Ne.def] at hp0
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

theorem snorm'_le_snorm'_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] (hf : AEStronglyMeasurable f μ) :
    snorm' f p μ ≤ snorm' f q μ := by
  have h_le_μ := snorm'_le_snorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ
#align measure_theory.snorm'_le_snorm'_of_exponent_le MeasureTheory.snorm'_le_snorm'_of_exponent_le

theorem snorm'_le_snormEssSup {q : ℝ} (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    snorm' f q μ ≤ snormEssSup f μ :=
  le_trans (snorm'_le_snormEssSup_mul_rpow_measure_univ hq_pos) (le_of_eq (by simp [measure_univ]))
#align measure_theory.snorm'_le_snorm_ess_sup MeasureTheory.snorm'_le_snormEssSup

theorem snorm_le_snorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) : snorm f p μ ≤ snorm f q μ :=
  (snorm_le_snorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))
#align measure_theory.snorm_le_snorm_of_exponent_le MeasureTheory.snorm_le_snorm_of_exponent_le

theorem snorm'_lt_top_of_snorm'_lt_top_of_exponent_le {p q : ℝ} [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : snorm' f q μ < ∞) (hp_nonneg : 0 ≤ p)
    (hpq : p ≤ q) : snorm' f p μ < ∞ := by
  rcases le_or_lt p 0 with hp_nonpos | hp_pos
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
  rw [← Ne.def] at hp0
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

end SameSpace

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {μ : Measure α}
  {f : α → E} {g : α → F}

theorem snorm'_le_snorm'_mul_snorm' {p q r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm' (fun x => b (f x) (g x)) p μ ≤ snorm' f q μ * snorm' g r μ := by
  rw [snorm']
  calc
    (∫⁻ a : α, ↑‖b (f a) (g a)‖₊ ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ↑(‖f a‖₊ * ‖g a‖₊) ^ p ∂μ) ^ (1 / p) :=
      (ENNReal.rpow_le_rpow_iff <| one_div_pos.mpr hp0_lt).mpr <|
        lintegral_mono_ae <|
          h.mono fun a ha => (ENNReal.rpow_le_rpow_iff hp0_lt).mpr <| ENNReal.coe_le_coe.mpr <| ha
    _ ≤ _ := ?_
  simp_rw [snorm', ENNReal.coe_mul]
  exact ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.ennnorm hg.ennnorm
#align measure_theory.snorm'_le_snorm'_mul_snorm' MeasureTheory.snorm'_le_snorm'_mul_snorm'

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem snorm_le_snorm_mul_snorm_of_nnnorm {p q r : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ := by
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
    exact snorm_le_snorm_top_mul_snorm p f hg b h
  by_cases hr_top : r = ∞
  · have hpq : p = q := by
      simpa only [hr_top, one_div, ENNReal.inv_top, add_zero, inv_inj] using hpqr
    rw [← hpq, hr_top]
    exact snorm_le_snorm_mul_snorm_top p hf g b h
  have hpq : p < q := by
    suffices 1 / q < 1 / p by rwa [one_div, one_div, ENNReal.inv_lt_inv] at this
    rw [hpqr]
    refine' ENNReal.lt_add_right _ _
    · simp only [hq_ne_zero, one_div, Ne.def, ENNReal.inv_eq_top, not_false_iff]
    · simp only [hr_top, one_div, Ne.def, ENNReal.inv_eq_zero, not_false_iff]
  rw [snorm_eq_snorm' hp_zero (hpq.trans_le le_top).ne, snorm_eq_snorm' hq_ne_zero hq_top,
    snorm_eq_snorm' hr_ne_zero hr_top]
  refine' snorm'_le_snorm'_mul_snorm' hf hg _ h _ _ _
  · exact ENNReal.toReal_pos hp_zero (hpq.trans_le le_top).ne
  · exact ENNReal.toReal_strict_mono hq_top hpq
  rw [← ENNReal.one_toReal, ← ENNReal.toReal_div, ← ENNReal.toReal_div, ← ENNReal.toReal_div, hpqr,
    ENNReal.toReal_add]
  · simp only [hq_ne_zero, one_div, Ne.def, ENNReal.inv_eq_top, not_false_iff]
  · simp only [hr_ne_zero, one_div, Ne.def, ENNReal.inv_eq_top, not_false_iff]
#align measure_theory.snorm_le_snorm_mul_snorm_of_nnnorm MeasureTheory.snorm_le_snorm_mul_snorm_of_nnnorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem snorm_le_snorm_mul_snorm'_of_norm {p q r : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ :=
  snorm_le_snorm_mul_snorm_of_nnnorm hf hg b h hpqr
#align measure_theory.snorm_le_snorm_mul_snorm'_of_norm MeasureTheory.snorm_le_snorm_mul_snorm'_of_norm

end Bilinear

section BoundedSMul

variable {𝕜 α E F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]
  [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [BoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [MulActionWithZero 𝕜 F] [BoundedSMul 𝕜 F]

theorem snorm'_smul_le_mul_snorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
  snorm'_le_snorm'_mul_snorm' hφ hf (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _)
    hp0_lt hpq hpqr
#align measure_theory.snorm'_smul_le_mul_snorm' MeasureTheory.snorm'_smul_le_mul_snorm'

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
theorem snorm_smul_le_mul_snorm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (φ • f) p μ ≤ snorm φ q μ * snorm f r μ :=
  (snorm_le_snorm_mul_snorm_of_nnnorm hφ hf (· • ·)
      (eventually_of_forall fun _ => nnnorm_smul_le _ _) hpqr :
    _)
#align measure_theory.snorm_smul_le_mul_snorm MeasureTheory.snorm_smul_le_mul_snorm

theorem Memℒp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f r μ) (hφ : Memℒp φ q μ)
    (hpqr : 1 / p = 1 / q + 1 / r) : Memℒp (φ • f) p μ :=
  ⟨hφ.1.smul hf.1,
    (snorm_smul_le_mul_snorm hf.1 hφ.1 hpqr).trans_lt
      (ENNReal.mul_lt_top hφ.snorm_ne_top hf.snorm_ne_top)⟩
#align measure_theory.mem_ℒp.smul MeasureTheory.Memℒp.smul

theorem Memℒp.smul_of_top_right {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f p μ)
    (hφ : Memℒp φ ∞ μ) : Memℒp (φ • f) p μ := by
  apply hf.smul hφ
  simp only [ENNReal.div_top, zero_add]
#align measure_theory.mem_ℒp.smul_of_top_right MeasureTheory.Memℒp.smul_of_top_right

theorem Memℒp.smul_of_top_left {p : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : Memℒp f ∞ μ)
    (hφ : Memℒp φ p μ) : Memℒp (φ • f) p μ := by
  apply hf.smul hφ
  simp only [ENNReal.div_top, add_zero]
#align measure_theory.mem_ℒp.smul_of_top_left MeasureTheory.Memℒp.smul_of_top_left

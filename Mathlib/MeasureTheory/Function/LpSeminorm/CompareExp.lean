/-
Copyright (c) 2020 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Eric Wieser
-/
module

public import Mathlib.Data.ENNReal.Holder
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Compare Lp seminorms for different values of `p`

In this file we compare `MeasureTheory.eLpNorm'` and `MeasureTheory.eLpNorm` for different
exponents.
-/

public section

open Filter ENNReal
open scoped Topology

namespace MeasureTheory

section SameSpace

variable {α ε ε' : Type*} {m : MeasurableSpace α} {μ : Measure α} {f : α → ε}
  [TopologicalSpace ε] [ContinuousENorm ε]
  [TopologicalSpace ε'] [ESeminormedAddMonoid ε']

theorem eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ {p q : ℝ} (hp0_lt : 0 < p) (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ ≤ eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) := by
  have hq0_lt : 0 < q := lt_of_lt_of_le hp0_lt hpq
  by_cases hpq_eq : p = q
  · rw [hpq_eq, sub_self, ENNReal.rpow_zero, mul_one]
  have hpq : p < q := lt_of_le_of_ne hpq hpq_eq
  let g := fun _ : α => (1 : ℝ≥0∞)
  have h_rw : (∫⁻ a, ‖f a‖ₑ ^ p ∂μ) = ∫⁻ a, (‖f a‖ₑ * g a) ^ p ∂μ :=
    lintegral_congr fun a => by simp [g]
  repeat' rw [eLpNorm'_eq_lintegral_enorm]
  rw [h_rw]
  let r := p * q / (q - p)
  have hpqr : 1 / p = 1 / q + 1 / r := by simp [field]
  calc
    (∫⁻ a : α, (‖f a‖ₑ * g a) ^ p ∂μ) ^ (1 / p) ≤
        (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) * (∫⁻ a : α, g a ^ r ∂μ) ^ (1 / r) :=
      ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hp0_lt hpq hpqr μ hf.enorm aemeasurable_const
    _ = (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ^ (1 / q) * μ Set.univ ^ (1 / p - 1 / q) := by
      rw [hpqr]; simp [r, g]

theorem eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ {q : ℝ} (hq_pos : 0 < q) :
    eLpNorm' f q μ ≤ eLpNormEssSup f μ * μ Set.univ ^ (1 / q) := by
  have h_le : (∫⁻ a : α, ‖f a‖ₑ ^ q ∂μ) ≤ ∫⁻ _ : α, eLpNormEssSup f μ ^ q ∂μ := by
    refine lintegral_mono_ae ?_
    have h_nnnorm_le_eLpNorm_ess_sup := enorm_ae_le_eLpNormEssSup f μ
    exact h_nnnorm_le_eLpNorm_ess_sup.mono fun x hx => by gcongr
  rw [eLpNorm', ← ENNReal.rpow_one (eLpNormEssSup f μ)]
  nth_rw 2 [← mul_inv_cancel₀ (ne_of_lt hq_pos).symm]
  rw [ENNReal.rpow_mul, one_div, ← ENNReal.mul_rpow_of_nonneg _ _ (by simp [hq_pos.le] : 0 ≤ q⁻¹)]
  gcongr
  rwa [lintegral_const] at h_le

theorem eLpNorm_le_eLpNorm_mul_rpow_measure_univ {p q : ℝ≥0∞} (hpq : p ≤ q)
    (hf : AEStronglyMeasurable f μ) :
    eLpNorm f p μ ≤ eLpNorm f q μ * μ Set.univ ^ (1 / p.toReal - 1 / q.toReal) := by
  obtain rfl | hp0 := eq_or_ne p 0
  · simp
  have hq0_lt : 0 < q := hp0.pos.trans_le hpq
  obtain rfl | hq_top := eq_or_ne q ∞
  · simp only [_root_.div_zero, one_div, ENNReal.toReal_top, sub_zero]
    obtain rfl | hp_top := eq_or_ne p ∞
    · simp
    rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
    have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_top
    refine (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hp_pos).trans (le_of_eq ?_)
    congr
    exact one_div _
  have hp_lt_top : p < ∞ := hpq.trans_lt (lt_top_iff_ne_top.mpr hq_top)
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_lt_top.ne
  rw [eLpNorm_eq_eLpNorm' hp0 hp_lt_top.ne, eLpNorm_eq_eLpNorm' hq0_lt.ne.symm hq_top]
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  exact eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq_real hf

theorem eLpNorm'_le_eLpNorm'_of_exponent_le {p q : ℝ} (hp0_lt : 0 < p)
    (hpq : p ≤ q) (μ : Measure α) [IsProbabilityMeasure μ] (hf : AEStronglyMeasurable f μ) :
    eLpNorm' f p μ ≤ eLpNorm' f q μ := by
  have h_le_μ := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp0_lt hpq hf
  rwa [measure_univ, ENNReal.one_rpow, mul_one] at h_le_μ

theorem eLpNorm'_le_eLpNormEssSup {q : ℝ} (hq_pos : 0 < q) [IsProbabilityMeasure μ] :
    eLpNorm' f q μ ≤ eLpNormEssSup f μ :=
  (eLpNorm'_le_eLpNormEssSup_mul_rpow_measure_univ hq_pos).trans_eq (by simp [measure_univ])

theorem eLpNorm_le_eLpNorm_of_exponent_le {p q : ℝ≥0∞} (hpq : p ≤ q) [IsProbabilityMeasure μ]
    (hf : AEStronglyMeasurable f μ) : eLpNorm f p μ ≤ eLpNorm f q μ :=
  (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hf).trans (le_of_eq (by simp [measure_univ]))

theorem eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le {p q : ℝ} [IsFiniteMeasure μ]
    (hf : AEStronglyMeasurable f μ) (hfq_lt_top : eLpNorm' f q μ < ∞) (hp_nonneg : 0 ≤ p)
    (hpq : p ≤ q) : eLpNorm' f p μ < ∞ := by
  rcases le_or_gt p 0 with hp_nonpos | hp_pos
  · rw [le_antisymm hp_nonpos hp_nonneg]
    simp
  have hq_pos : 0 < q := lt_of_lt_of_le hp_pos hpq
  calc
    eLpNorm' f p μ ≤ eLpNorm' f q μ * μ Set.univ ^ (1 / p - 1 / q) :=
      eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ hp_pos hpq hf
    _ < ∞ := by
      rw [ENNReal.mul_lt_top_iff]
      refine Or.inl ⟨hfq_lt_top, ENNReal.rpow_lt_top_of_nonneg ?_ (by finiteness)⟩
      rwa [le_sub_comm, sub_zero, one_div, one_div, inv_le_inv₀ hq_pos hp_pos]

theorem MemLp.mono_exponent {p q : ℝ≥0∞} [IsFiniteMeasure μ] (hfq : MemLp f q μ)
    (hpq : p ≤ q) : MemLp f p μ := by
  obtain ⟨hfq_m, hfq_lt_top⟩ := hfq
  by_cases hp0 : p = 0
  · rwa [hp0, memLp_zero_iff_aestronglyMeasurable]
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
    exact ENNReal.rpow_lt_top_of_nonneg (by simp [hp_pos.le]) (by finiteness)
  have hq0 : q ≠ 0 := by
    by_contra hq_eq_zero
    obtain rfl : p = 0 := le_antisymm (by rwa [hq_eq_zero] at hpq) zero_le
    rw [ENNReal.toReal_zero] at hp_pos
    exact (lt_irrefl _) hp_pos
  have hpq_real : p.toReal ≤ q.toReal := ENNReal.toReal_mono hq_top hpq
  rw [eLpNorm_eq_eLpNorm' hp0 hp_top]
  rw [eLpNorm_eq_eLpNorm' hq0 hq_top] at hfq_lt_top
  exact eLpNorm'_lt_top_of_eLpNorm'_lt_top_of_exponent_le hfq_m hfq_lt_top hp_pos.le hpq_real

/-- If a function is supported on a finite-measure set and belongs to `ℒ^p`, then it belongs to
`ℒ^q` for any `q ≤ p`. -/
lemma MemLp.mono_exponent_of_measure_support_ne_top {p q : ℝ≥0∞} {f : α → ε'} (hfq : MemLp f q μ)
    {s : Set α} (hf : ∀ x, x ∉ s → f x = 0) (hs : μ s ≠ ∞) (hpq : p ≤ q) : MemLp f p μ := by
  have : (toMeasurable μ s).indicator f = f := by
    apply Set.indicator_eq_self.2
    apply Function.support_subset_iff'.2 fun x hx ↦ hf x ?_
    contrapose hx
    exact subset_toMeasurable μ s hx
  rw [← this, memLp_indicator_iff_restrict (measurableSet_toMeasurable μ s)] at hfq ⊢
  have : Fact (μ (toMeasurable μ s) < ∞) := ⟨by simpa [lt_top_iff_ne_top] using hs⟩
  exact hfq.mono_exponent hpq

end SameSpace

section Bilinear

variable {α E F G : Type*} {m : MeasurableSpace α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G] {μ : Measure α}
  {f : α → E} {g : α → F}

open NNReal

theorem eLpNorm_le_eLpNorm_top_mul_eLpNorm (p : ℝ≥0∞) (f : α → E) {g : α → F}
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f ∞ μ * eLpNorm g p μ := by
  calc
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ eLpNorm (fun x => (c : ℝ) • ‖f x‖ * ‖g x‖) p μ :=
      eLpNorm_mono_ae_real h
    _ ≤ c * eLpNorm f ∞ μ * eLpNorm g p μ := ?_
  simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal c.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
  gcongr
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp
  · rw [← eLpNorm_norm f, ← eLpNorm_norm g]
    simp_rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm, enorm_mul, enorm_norm]
    exact ENNReal.essSup_mul_le (‖f ·‖ₑ) (‖g ·‖ₑ)
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₁.ne' hp₂.ne, eLpNorm_exponent_top,
    eLpNormEssSup, one_div, ENNReal.rpow_inv_le_iff hp, enorm_mul, enorm_norm]
  rw [ENNReal.mul_rpow_of_nonneg (hz := hp.le), ENNReal.rpow_inv_rpow hp.ne',
    ← lintegral_const_mul'' _ (by fun_prop)]
  simp only [← ENNReal.mul_rpow_of_nonneg (hz := hp.le)]
  apply lintegral_mono_ae
  filter_upwards [h, enorm_ae_le_eLpNormEssSup f μ] with x hb hf
  gcongr
  exact hf

theorem eLpNorm_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → F) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) :
    eLpNorm (fun x => b (f x) (g x)) p μ ≤ c * eLpNorm f p μ * eLpNorm g ∞ μ :=
  calc
    eLpNorm (fun x ↦ b (f x) (g x)) p μ ≤ c * eLpNorm g ∞ μ * eLpNorm f p μ :=
      eLpNorm_le_eLpNorm_top_mul_eLpNorm p g hf (flip b) c <| by
        convert h using 3 with x
        simp only [mul_assoc, mul_comm ‖f x‖₊]
    _ = c * eLpNorm f p μ * eLpNorm g ∞ μ := by
      simp only [mul_assoc]; rw [mul_comm (eLpNorm _ _ _)]

theorem eLpNorm'_le_eLpNorm'_mul_eLpNorm' {p q r : ℝ} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) (hro_lt : 0 < r) (hrp : r < p)
    (hpqr : 1 / r = 1 / p + 1 / q) :
    eLpNorm' (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
  calc
    eLpNorm' (fun x => b (f x) (g x)) r μ
      ≤ eLpNorm' (fun x ↦ (c : ℝ) • ‖f x‖ * ‖g x‖) r μ := by
      simp only [eLpNorm']
      gcongr ?_ ^ _
      refine lintegral_mono_ae <| h.mono fun a ha ↦ ?_
      gcongr
      simp only [enorm_eq_nnnorm, ENNReal.coe_le_coe]
      simpa using ha
    _ ≤ c * eLpNorm' f p μ * eLpNorm' g q μ := by
      simp only [smul_mul_assoc, ← Pi.smul_def, eLpNorm'_const_smul _ hro_lt]
      rw [Real.enorm_eq_ofReal c.coe_nonneg, ENNReal.ofReal_coe_nnreal, mul_assoc]
      gcongr
      simpa only [eLpNorm', enorm_mul, enorm_norm] using
        ENNReal.lintegral_Lp_mul_le_Lq_mul_Lr hro_lt hrp hpqr μ hf.enorm hg.enorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm {p q r : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ := by
  have hpqr := hpqr.one_div_eq
  obtain (rfl | rfl | hp) := ENNReal.trichotomy p
  · simp_all
  · have : r = q := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_top_mul_eLpNorm r f hg b c h
  obtain (rfl | rfl | hq) := ENNReal.trichotomy q
  · simp_all
  · have : r = p := by simpa using hpqr
    exact this ▸ eLpNorm_le_eLpNorm_mul_eLpNorm_top p hf g b c h
  obtain ⟨hp₁, hp₂⟩ := ENNReal.toReal_pos_iff.mp hp
  obtain ⟨hq₁, hq₂⟩ := ENNReal.toReal_pos_iff.mp hq
  have hpqr' : 1 / r.toReal = 1 / p.toReal + 1 / q.toReal := by
    have := congr(ENNReal.toReal $(hpqr))
    rw [ENNReal.toReal_add (by simpa using hp₁.ne') (by simpa using hq₁.ne')] at this
    simpa
  have hr : 0 < r.toReal := one_div_pos.mp <| by rw [hpqr']; positivity
  obtain ⟨hr₁, hr₂⟩ := ENNReal.toReal_pos_iff.mp hr
  have hrp : r.toReal < p.toReal := lt_of_one_div_lt_one_div hp <|
    hpqr' ▸ lt_add_of_pos_right _ (by positivity)
  rw [eLpNorm_eq_eLpNorm', eLpNorm_eq_eLpNorm', eLpNorm_eq_eLpNorm']
  · exact eLpNorm'_le_eLpNorm'_mul_eLpNorm' hf hg b c h hr hrp hpqr'
  all_goals first | positivity | finiteness

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm {p q r : ℝ≥0∞} (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (b : E → F → G) (c : ℝ≥0)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ c * ‖f x‖ * ‖g x‖) [hpqr : HolderTriple p q r] :
    eLpNorm (fun x => b (f x) (g x)) r μ ≤ c * eLpNorm f p μ * eLpNorm g q μ :=
  eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf hg b c h

open NNReal in
theorem MemLp.of_bilin {p q r : ℝ≥0∞} {f : α → E} {g : α → F} (b : E → F → G) (c : ℝ≥0)
    (hf : MemLp f p μ) (hg : MemLp g q μ)
    (h : AEStronglyMeasurable (fun x ↦ b (f x) (g x)) μ)
    (hb : ∀ᵐ (x : α) ∂μ, ‖b (f x) (g x)‖₊ ≤ c * ‖f x‖₊ * ‖g x‖₊)
    [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ b (f x) (g x)) r μ := by
  refine ⟨h, ?_⟩
  apply (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hf.1 hg.1 b c hb (hpqr := hpqr)).trans_lt
  finiteness [hf.2, hg.2]

end Bilinear

section IsBoundedSMul

variable {𝕜 α E F : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedRing 𝕜]
  [NormedAddCommGroup E] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
  [NormedAddCommGroup F] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F] {f : α → E}

theorem eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (p : ℝ≥0∞) (hf : AEStronglyMeasurable f μ)
    (φ : α → 𝕜) : eLpNorm (φ • f) p μ ≤ eLpNorm φ ∞ μ * eLpNorm f p μ := by
  simpa using (eLpNorm_le_eLpNorm_top_mul_eLpNorm p φ hf (· • ·) 1
    (.of_forall fun _ => by simpa using nnnorm_smul_le _ _) :)

theorem eLpNorm_smul_le_eLpNorm_mul_eLpNorm_top (p : ℝ≥0∞) (f : α → E) {φ : α → 𝕜}
    (hφ : AEStronglyMeasurable φ μ) : eLpNorm (φ • f) p μ ≤ eLpNorm φ p μ * eLpNorm f ∞ μ := by
  simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_top p hφ f (· • ·) 1
    (.of_forall fun _ => by simpa using nnnorm_smul_le _ _) :)

theorem eLpNorm'_smul_le_mul_eLpNorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : eLpNorm' (φ • f) p μ ≤ eLpNorm' φ q μ * eLpNorm' f r μ := by
  simpa using eLpNorm'_le_eLpNorm'_mul_eLpNorm' hφ hf (· • ·) 1
    (.of_forall fun _ => by simpa using nnnorm_smul_le _ _)
    hp0_lt hpq hpqr

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of a scalar product `φ • f`. -/
theorem eLpNorm_smul_le_mul_eLpNorm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) [hpqr : HolderTriple p q r] :
    eLpNorm (φ • f) r μ ≤ eLpNorm φ p μ * eLpNorm f q μ := by
  simpa using (eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm hφ hf (· • ·) 1
      (.of_forall fun _ => by simpa using nnnorm_smul_le _ _) : _)

theorem MemLp.smul {p q r : ℝ≥0∞} {f : α → E} {φ : α → 𝕜} (hf : MemLp f q μ) (hφ : MemLp φ p μ)
    [hpqr : HolderTriple p q r] : MemLp (φ • f) r μ :=
  ⟨hφ.1.smul hf.1,
    eLpNorm_smul_le_mul_eLpNorm hf.1 hφ.1 |>.trans_lt <|
      ENNReal.mul_lt_top hφ.eLpNorm_lt_top hf.eLpNorm_lt_top⟩

end IsBoundedSMul

section Mul

variable {α : Type*} {_ : MeasurableSpace α} {𝕜 : Type*} [NormedRing 𝕜] {μ : Measure α}
  {p q r : ℝ≥0∞} {f : α → 𝕜} {φ : α → 𝕜}

theorem MemLp.mul (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (φ * f) r μ :=
  MemLp.smul hf hφ

/-- Variant of `MemLp.mul` where the function is written as `fun x ↦ φ x * f x`
instead of `φ * f`. -/
theorem MemLp.mul' (hf : MemLp f q μ) (hφ : MemLp φ p μ) [hpqr : HolderTriple p q r] :
    MemLp (fun x ↦ φ x * f x) r μ :=
  MemLp.smul hf hφ

end Mul

section Prod
variable {ι α 𝕜 : Type*} {_ : MeasurableSpace α} [NormedCommRing 𝕜] {μ : Measure α} {f : ι → α → 𝕜}
  {p : ι → ℝ≥0∞} {s : Finset ι}

open Finset in
/-- See `MemLp.prod'` for the applied version. -/
protected lemma MemLp.prod (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) :
    MemLp (∏ i ∈ s, f i) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ := by
  induction s using cons_induction with
  | empty =>
    by_cases hμ : μ = 0 <;>
      simp [MemLp, eLpNormEssSup_const, hμ, aestronglyMeasurable_const, Pi.one_def]
  | cons i s hi ih =>
    rw [prod_cons]
    exact (ih <| forall_of_forall_cons hf).mul (hf i <| mem_cons_self ..) (hpqr := ⟨by simp⟩)

/-- See `MemLp.prod` for the unapplied version. -/
protected lemma MemLp.prod' (hf : ∀ i ∈ s, MemLp (f i) (p i) μ) :
    MemLp (fun ω ↦ ∏ i ∈ s, f i ω) (∑ i ∈ s, (p i)⁻¹)⁻¹ μ := by
  simpa [Finset.prod_fn] using MemLp.prod hf

end Prod
end MeasureTheory

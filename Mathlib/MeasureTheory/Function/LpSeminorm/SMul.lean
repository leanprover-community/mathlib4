import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

open scoped NNReal ENNReal

namespace MeasureTheory

variable {α E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

section Monotonicity

variable {_ : MeasurableSpace α} {μ : Measure α} {f : α → E} {g : α → F} {p : ℝ≥0∞}

theorem snorm_le_of_nnnorm_ae_le_mul_nnnorm_of_one_le {c : ℝ≥0} (h : (‖f ·‖₊) ≤ᵐ[μ] (c * ‖g ·‖₊))
    (hp : 1 ≤ p) : snorm f p μ ≤ c • snorm g p μ := by
  induction p using ENNReal.recTopCoe with
  | top =>
    simp only [snorm_exponent_top, ENNReal.smul_def, smul_eq_mul, ← ENNReal.essSup_const_mul]
    refine essSup_mono_ae <| h.mono fun x hx ↦ ?_
    simpa only [ENNReal.coe_mul] using ENNReal.coe_le_coe.2 hx
  | coe p =>
    norm_cast at hp
    simp only [snorm_coe_of_one_le _ hp]
    calc
      (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ (p : ℝ) ∂μ) ^ (1 / p : ℝ) ≤
          (∫⁻ x, (c * ‖g x‖₊ : ℝ≥0∞) ^ (p : ℝ) ∂μ) ^ (1 / p : ℝ) := by
        gcongr (?_ : ℝ≥0∞) ^ _
        refine lintegral_mono_ae <| h.mono fun x hx ↦ ?_
        gcongr
        assumption_mod_cast
      _ = c • (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ (p : ℝ) ∂μ) ^ (1 / p : ℝ) := by
        have hcp : (c : ℝ≥0∞) ^ (p : ℝ) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg p.2 ENNReal.coe_ne_top
        have hp' : (0 : ℝ) ≤ 1 / p := by positivity
        simp only [ENNReal.mul_rpow_of_nonneg, hp', p.coe_nonneg, lintegral_const_mul' _ _ hcp]
        rw [← ENNReal.rpow_mul, mul_one_div_cancel, ENNReal.rpow_one, ENNReal.smul_def, smul_eq_mul]
        exact (NNReal.coe_pos.2 <| one_pos.trans_le hp).ne'
#align measure_theory.snorm'_le_nnreal_smul_snorm'_of_ae_le_mul MeasureTheory.snorm_le_of_nnnorm_ae_le_mul_nnnorm_of_one_le
#align measure_theory.snorm_ess_sup_le_nnreal_smul_snorm_ess_sup_of_ae_le_mul MeasureTheory.snorm_le_of_nnnorm_ae_le_mul_nnnorm_of_one_le
#align measure_theory.snorm_le_nnreal_smul_snorm_of_ae_le_mul MeasureTheory.snorm_le_of_nnnorm_ae_le_mul_nnnorm_of_one_le

lemma snorm_le_of_nnnorm_ae_le_mul_nnnorm_of_le_one {c : ℝ≥0} (h : (‖f ·‖₊) ≤ᵐ[μ] (c * ‖g ·‖₊))
    (hp : p ≤ 1) : snorm f p μ ≤ c ^ p.toReal • snorm g p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · suffices f.support ≤ᵐ[μ] g.support by simpa using measure_mono_ae this
    refine h.mono fun x hx ↦ mt fun hg ↦ ?_
    simpa [hg] using hx
  · simp only [snorm_of_ne_zero_le_one _ hp0 hp]
    calc
      ∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ ≤ ∫⁻ x, (c * ‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ :=
        lintegral_mono_ae <| h.mono fun x hx ↦ by gcongr; assumption_mod_cast
      _ = c ^ p.toReal • ∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ := by
        have hcp : (c : ℝ≥0∞) ^ p.toReal ≠ ∞ :=
          ENNReal.rpow_ne_top_of_nonneg p.toReal_nonneg ENNReal.coe_ne_top
        simp only [ENNReal.mul_rpow_of_nonneg _ _ p.toReal_nonneg, lintegral_const_mul']
        
    
    

-- TODO: add the whole family of lemmas?
private theorem le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg {α} [LinearOrderedSemiring α]
    {a b c : α} (ha : 0 ≤ a) (hb : b < 0) (hc : 0 ≤ c) : a ≤ b * c ↔ a = 0 ∧ c = 0 := by
  constructor
  · intro h
    exact
      ⟨(h.trans (mul_nonpos_of_nonpos_of_nonneg hb.le hc)).antisymm ha,
        (nonpos_of_mul_nonneg_right (ha.trans h) hb).antisymm hc⟩
  · rintro ⟨rfl, rfl⟩
    rw [mul_zero]

/-- When `c` is negative, `‖f x‖ ≤ c * ‖g x‖` is nonsense and forces both `f` and `g` to have an
`snorm` of `0`. -/
theorem snorm_eq_zero_and_zero_of_ae_le_mul_neg {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (hc : c < 0) (p : ℝ≥0∞) :
    snorm f p μ = 0 ∧ snorm g p μ = 0 := by
  simp_rw [le_mul_iff_eq_zero_of_nonneg_of_neg_of_nonneg (norm_nonneg _) hc (norm_nonneg _),
    norm_eq_zero, eventually_and] at h
  change f =ᵐ[μ] 0 ∧ g =ᵐ[μ] 0 at h
  simp [snorm_congr_ae h.1, snorm_congr_ae h.2]
#align measure_theory.snorm_eq_zero_and_zero_of_ae_le_mul_neg MeasureTheory.snorm_eq_zero_and_zero_of_ae_le_mul_neg

theorem snorm_le_mul_snorm_of_ae_le_mul {f : α → F} {g : α → G} {c : ℝ}
    (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) (p : ℝ≥0∞) : snorm f p μ ≤ ENNReal.ofReal c * snorm g p μ :=
  snorm_le_nnreal_smul_snorm_of_ae_le_mul
    (h.mono fun _x hx => hx.trans <| mul_le_mul_of_nonneg_right c.le_coe_toNNReal (norm_nonneg _)) _
#align measure_theory.snorm_le_mul_snorm_of_ae_le_mul MeasureTheory.snorm_le_mul_snorm_of_ae_le_mul

theorem Memℒp.of_nnnorm_le_mul {f : α → E} {g : α → F} {c : ℝ≥0} (hg : Memℒp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖₊ ≤ c * ‖g x‖₊) : Memℒp f p μ :=
  ⟨hf,
    (snorm_le_nnreal_smul_snorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.coe_ne_top hg.snorm_ne_top⟩
#align measure_theory.mem_ℒp.of_nnnorm_le_mul MeasureTheory.Memℒp.of_nnnorm_le_mul

theorem Memℒp.of_le_mul {f : α → E} {g : α → F} {c : ℝ} (hg : Memℒp g p μ)
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ c * ‖g x‖) : Memℒp f p μ :=
  ⟨hf,
    (snorm_le_mul_snorm_of_ae_le_mul hfg p).trans_lt <|
      ENNReal.mul_lt_top ENNReal.ofReal_ne_top hg.snorm_ne_top⟩
#align measure_theory.mem_ℒp.of_le_mul MeasureTheory.Memℒp.of_le_mul

theorem snorm'_le_snorm'_mul_snorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {g : α → F} (hg : AEStronglyMeasurable g μ) (b : E → F → G)
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

theorem snorm_le_snorm_top_mul_snorm (p : ℝ≥0∞) (f : α → E) {g : α → F}
    (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f ∞ μ * snorm g p μ := by
  by_cases hp_top : p = ∞
  · simp_rw [hp_top, snorm_exponent_top]
    refine' le_trans (essSup_mono_ae <| h.mono fun a ha => _) (ENNReal.essSup_mul_le _ _)
    simp_rw [Pi.mul_apply, ← ENNReal.coe_mul, ENNReal.coe_le_coe]
    exact ha
  by_cases hp_zero : p = 0
  · simp only [hp_zero, snorm_exponent_zero, mul_zero, le_zero_iff]
  simp_rw [snorm_eq_lintegral_rpow_nnnorm hp_zero hp_top, snorm_exponent_top, snormEssSup]
  calc
    (∫⁻ x, (‖b (f x) (g x)‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) ≤
        (∫⁻ x, (‖f x‖₊ : ℝ≥0∞) ^ p.toReal * (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      refine' ENNReal.rpow_le_rpow _ (one_div_nonneg.mpr ENNReal.toReal_nonneg)
      refine' lintegral_mono_ae (h.mono fun a ha => _)
      rw [← ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
      refine' ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
      rw [← ENNReal.coe_mul, ENNReal.coe_le_coe]
      exact ha
    _ ≤
        (∫⁻ x, essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ ^ p.toReal * (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^
          (1 / p.toReal) := by
      refine' ENNReal.rpow_le_rpow _ _
      swap;
      · rw [one_div_nonneg]
        exact ENNReal.toReal_nonneg
      refine' lintegral_mono_ae _
      filter_upwards [@ENNReal.ae_le_essSup _ _ μ fun x => (‖f x‖₊ : ℝ≥0∞)] with x hx
      exact mul_le_mul_right' (ENNReal.rpow_le_rpow hx ENNReal.toReal_nonneg) _
    _ = essSup (fun x => (‖f x‖₊ : ℝ≥0∞)) μ *
        (∫⁻ x, (‖g x‖₊ : ℝ≥0∞) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
      rw [lintegral_const_mul'']
      swap; · exact hg.nnnorm.aemeasurable.coe_nnreal_ennreal.pow aemeasurable_const
      rw [ENNReal.mul_rpow_of_nonneg]
      swap;
      · rw [one_div_nonneg]
        exact ENNReal.toReal_nonneg
      rw [← ENNReal.rpow_mul, one_div, mul_inv_cancel, ENNReal.rpow_one]
      rw [Ne.def, ENNReal.toReal_eq_zero_iff, not_or]
      exact ⟨hp_zero, hp_top⟩
#align measure_theory.snorm_le_snorm_top_mul_snorm MeasureTheory.snorm_le_snorm_top_mul_snorm

theorem snorm_le_snorm_mul_snorm_top (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (g : α → F) (b : E → F → G) (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖₊ ≤ ‖f x‖₊ * ‖g x‖₊) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f p μ * snorm g ∞ μ := by
  rw [← snorm_norm f, ← snorm_norm g]
  refine' (snorm_mono_ae_real h).trans _
  simp_rw [mul_comm ‖f _‖₊, val_eq_coe, NNReal.coe_mul, coe_nnnorm]
  rw [mul_comm]
  refine' snorm_le_snorm_top_mul_snorm p (fun x => ‖g x‖) hf.norm _ (h.mono fun x _ => _)
  simp_rw [nnnorm_mul]
  rfl
#align measure_theory.snorm_le_snorm_mul_snorm_top MeasureTheory.snorm_le_snorm_mul_snorm_top

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem snorm_le_snorm_mul_snorm_of_nnnorm {p q r : ℝ≥0∞} {f : α → E}
    (hf : AEStronglyMeasurable f μ) {g : α → F} (hg : AEStronglyMeasurable g μ) (b : E → F → G)
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
    · simp only [hq_ne_zero, one_div, Ne, ENNReal.inv_eq_top, not_false_iff]
    · simp only [hr_top, one_div, Ne, ENNReal.inv_eq_zero, not_false_iff]
  rw [snorm_eq_snorm' hp_zero (hpq.trans_le le_top).ne, snorm_eq_snorm' hq_ne_zero hq_top,
    snorm_eq_snorm' hr_ne_zero hr_top]
  refine' snorm'_le_snorm'_mul_snorm' hf hg _ h _ _ _
  · exact ENNReal.toReal_pos hp_zero (hpq.trans_le le_top).ne
  · exact ENNReal.toReal_strict_mono hq_top hpq
  rw [← ENNReal.one_toReal, ← ENNReal.toReal_div, ← ENNReal.toReal_div, ← ENNReal.toReal_div, hpqr,
    ENNReal.toReal_add]
  · simp only [hq_ne_zero, one_div, Ne, ENNReal.inv_eq_top, not_false_iff]
  · simp only [hr_ne_zero, one_div, Ne, ENNReal.inv_eq_top, not_false_iff]
#align measure_theory.snorm_le_snorm_mul_snorm_of_nnnorm MeasureTheory.snorm_le_snorm_mul_snorm_of_nnnorm

/-- Hölder's inequality, as an inequality on the `ℒp` seminorm of an elementwise operation
`fun x => b (f x) (g x)`. -/
theorem snorm_le_snorm_mul_snorm'_of_norm {p q r : ℝ≥0∞} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {g : α → F} (hg : AEStronglyMeasurable g μ) (b : E → F → G)
    (h : ∀ᵐ x ∂μ, ‖b (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖) (hpqr : 1 / p = 1 / q + 1 / r) :
    snorm (fun x => b (f x) (g x)) p μ ≤ snorm f q μ * snorm g r μ :=
  snorm_le_snorm_mul_snorm_of_nnnorm hf hg b h hpqr
#align measure_theory.snorm_le_snorm_mul_snorm'_of_norm MeasureTheory.snorm_le_snorm_mul_snorm'_of_norm

end Monotonicity

/-!
### Bounded actions by normed rings
In this section we show inequalities on the norm.
-/

section BoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [MulActionWithZero 𝕜 F]

variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜 F]

theorem snorm'_const_smul_le (c : 𝕜) (f : α → F) (hq_pos : 0 < q) :
    snorm' (c • f) q μ ≤ ‖c‖₊ • snorm' f q μ :=
  snorm'_le_nnreal_smul_snorm'_of_ae_le_mul (eventually_of_forall fun _ => nnnorm_smul_le _ _)
    hq_pos
#align measure_theory.snorm'_const_smul_le MeasureTheory.snorm'_const_smul_le

theorem snormEssSup_const_smul_le (c : 𝕜) (f : α → F) :
    snormEssSup (c • f) μ ≤ ‖c‖₊ • snormEssSup f μ :=
  snormEssSup_le_nnreal_smul_snormEssSup_of_ae_le_mul
    (eventually_of_forall fun _ => nnnorm_smul_le _ _)
#align measure_theory.snorm_ess_sup_const_smul_le MeasureTheory.snormEssSup_const_smul_le

theorem snorm_const_smul_le (c : 𝕜) (f : α → F) : snorm (c • f) p μ ≤ ‖c‖₊ • snorm f p μ :=
  snorm_le_nnreal_smul_snorm_of_ae_le_mul (eventually_of_forall fun _ => nnnorm_smul_le _ _) _
#align measure_theory.snorm_const_smul_le MeasureTheory.snorm_const_smul_le

theorem Memℒp.const_smul {f : α → E} (hf : Memℒp f p μ) (c : 𝕜) : Memℒp (c • f) p μ :=
  ⟨AEStronglyMeasurable.const_smul hf.1 c,
    (snorm_const_smul_le c f).trans_lt (ENNReal.mul_lt_top ENNReal.coe_ne_top hf.2.ne)⟩
#align measure_theory.mem_ℒp.const_smul MeasureTheory.Memℒp.const_smul

theorem Memℒp.const_mul {R} [NormedRing R] {f : α → R} (hf : Memℒp f p μ) (c : R) :
    Memℒp (fun x => c * f x) p μ :=
  hf.const_smul c
#align measure_theory.mem_ℒp.const_mul MeasureTheory.Memℒp.const_mul

theorem snorm'_smul_le_mul_snorm' {p q r : ℝ} {f : α → E} (hf : AEStronglyMeasurable f μ)
    {φ : α → 𝕜} (hφ : AEStronglyMeasurable φ μ) (hp0_lt : 0 < p) (hpq : p < q)
    (hpqr : 1 / p = 1 / q + 1 / r) : snorm' (φ • f) p μ ≤ snorm' φ q μ * snorm' f r μ :=
  snorm'_le_snorm'_mul_snorm' hφ hf (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _)
    hp0_lt hpq hpqr
#align measure_theory.snorm'_smul_le_mul_snorm' MeasureTheory.snorm'_smul_le_mul_snorm'

theorem snorm_smul_le_snorm_top_mul_snorm (p : ℝ≥0∞) {f : α → E} (hf : AEStronglyMeasurable f μ)
    (φ : α → 𝕜) : snorm (φ • f) p μ ≤ snorm φ ∞ μ * snorm f p μ :=
  (snorm_le_snorm_top_mul_snorm p φ hf (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _) :
    _)
#align measure_theory.snorm_smul_le_snorm_top_mul_snorm MeasureTheory.snorm_smul_le_snorm_top_mul_snorm

theorem snorm_smul_le_snorm_mul_snorm_top (p : ℝ≥0∞) (f : α → E) {φ : α → 𝕜}
    (hφ : AEStronglyMeasurable φ μ) : snorm (φ • f) p μ ≤ snorm φ p μ * snorm f ∞ μ :=
  (snorm_le_snorm_mul_snorm_top p hφ f (· • ·) (eventually_of_forall fun _ => nnnorm_smul_le _ _) :
    _)
#align measure_theory.snorm_smul_le_snorm_mul_snorm_top MeasureTheory.snorm_smul_le_snorm_mul_snorm_top

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

end BoundedSMul

/-!
### Bounded actions by normed division rings
The inequalities in the previous section are now tight.
-/


section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [MulActionWithZero 𝕜 E] [Module 𝕜 F]

variable [BoundedSMul 𝕜 E] [BoundedSMul 𝕜 F]

theorem snorm'_const_smul {f : α → F} (c : 𝕜) (hq_pos : 0 < q) :
    snorm' (c • f) q μ = ‖c‖₊ • snorm' f q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp [snorm', hq_pos]
  refine' le_antisymm (snorm'_const_smul_le _ _ hq_pos) _
  have : snorm' _ q μ ≤ _ := snorm'_const_smul_le c⁻¹ (c • f) hq_pos
  rwa [inv_smul_smul₀ hc, nnnorm_inv, ENNReal.le_inv_smul_iff (nnnorm_ne_zero_iff.mpr hc)] at this
#align measure_theory.snorm'_const_smul MeasureTheory.snorm'_const_smul

theorem snormEssSup_const_smul (c : 𝕜) (f : α → F) :
    snormEssSup (c • f) μ = (‖c‖₊ : ℝ≥0∞) * snormEssSup f μ := by
  simp_rw [snormEssSup, Pi.smul_apply, nnnorm_smul, ENNReal.coe_mul, ENNReal.essSup_const_mul]
#align measure_theory.snorm_ess_sup_const_smul MeasureTheory.snormEssSup_const_smul

theorem snorm_const_smul (c : 𝕜) (f : α → F) :
    snorm (c • f) p μ = (‖c‖₊ : ℝ≥0∞) * snorm f p μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine' le_antisymm (snorm_const_smul_le _ _) _
  have : snorm _ p μ ≤ _ := snorm_const_smul_le c⁻¹ (c • f)
  rwa [inv_smul_smul₀ hc, nnnorm_inv, ENNReal.le_inv_smul_iff (nnnorm_ne_zero_iff.mpr hc)] at this
#align measure_theory.snorm_const_smul MeasureTheory.snorm_const_smul

end NormedSpace

theorem snorm_indicator_ge_of_bdd_below (hp : p ≠ 0) (hp' : p ≠ ∞) {f : α → F} (C : ℝ≥0) {s : Set α}
    (hs : MeasurableSet s) (hf : ∀ᵐ x ∂μ, x ∈ s → C ≤ ‖s.indicator f x‖₊) :
    C • μ s ^ (1 / p.toReal) ≤ snorm (s.indicator f) p μ := by
  rw [ENNReal.smul_def, smul_eq_mul, snorm_eq_lintegral_rpow_nnnorm hp hp',
    ENNReal.le_rpow_one_div_iff (ENNReal.toReal_pos hp hp'),
    ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg, ← ENNReal.rpow_mul,
    one_div_mul_cancel (ENNReal.toReal_pos hp hp').ne.symm, ENNReal.rpow_one, ← set_lintegral_const,
    ← lintegral_indicator _ hs]
  refine' lintegral_mono_ae _
  filter_upwards [hf] with x hx
  rw [nnnorm_indicator_eq_indicator_nnnorm]
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs] at hx ⊢
    exact ENNReal.rpow_le_rpow (ENNReal.coe_le_coe.2 (hx hxs)) ENNReal.toReal_nonneg
  · simp [Set.indicator_of_not_mem hxs]
#align measure_theory.snorm_indicator_ge_of_bdd_below MeasureTheory.snorm_indicator_ge_of_bdd_below

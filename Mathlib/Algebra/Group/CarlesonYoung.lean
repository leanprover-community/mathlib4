/-
Copyright (c) 2025
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.Convolution

-- Copied from https://github.com/fpvandoorn/carleson/blob/b6c336e71d6a663c11c948e816674e3c6a8d1364/Carleson/ToMathlib/MeasureTheory/Integral/MeanInequalities.lean
-- All of the theorem statements are unchanged, but some proofs are `sorry`'d due to missing dependencies from Carleson

set_option linter.style.header false

open NNReal ENNReal MeasureTheory Finset

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

namespace ENNReal

-- Add after `lintegral_prod_norm_pow_le`
/-- A version of Hölder with multiple arguments, allowing `∞` as an exponent. -/
theorem lintegral_prod_norm_pow_le' {α ι : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Finset ι} {f : ι → α → ℝ≥0∞} (hf : ∀ i ∈ s, AEMeasurable (f i) μ)
    {p : ι → ℝ≥0∞} (hp : ∑ i ∈ s, (p i)⁻¹ = 1) :
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ := by
  classical
  revert hp hf
  refine Finset.strongInduction (fun s hs hf hp ↦ ?_) s (p := fun s ↦
    (∀ i ∈ s, AEMeasurable (f i) μ) → (∑ i ∈ s, (p i)⁻¹ = 1) →
    ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ ≤ ∏ i ∈ s, eLpNorm (f i) (p i) μ)
  by_cases exists_top : ∃ i₀ ∈ s, p i₀ = ∞    -- If one of the exponents is `∞`, we reduce to the
  · obtain ⟨i₀, hi₀, pi₀_eq_top⟩ := exists_top -- case without it and use the inductive hypothesis
    calc ∫⁻ (a : α), ∏ i ∈ s, f i a ∂μ
      _ = ∫⁻ (a : α), f i₀ a * ∏ i ∈ s.erase i₀, f i a ∂μ :=
        lintegral_congr (fun a ↦ (Finset.mul_prod_erase s (f · a) hi₀).symm)
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∫⁻ (a : α), ∏ i ∈ s.erase i₀, f i a ∂μ := by
        rw [← lintegral_const_mul'', pi₀_eq_top]
        · exact lintegral_mono_ae <| (ae_le_essSup (f i₀)).mono (fun a ha ↦ mul_le_mul_right' ha _)
        · exact Finset.aemeasurable_prod _ (fun i hi ↦ hf i (Finset.mem_of_mem_erase hi))
      _ ≤ eLpNorm (f i₀) (p i₀) μ * ∏ i ∈ s.erase i₀, eLpNorm (f i) (p i) μ := by
        apply mul_left_mono
        apply hs (s.erase i₀) (s.erase_ssubset hi₀) (fun i hi ↦ hf i (s.erase_subset i₀ hi))
        simpa [← Finset.add_sum_erase s _ hi₀, pi₀_eq_top] using hp
      _ = _ := Finset.mul_prod_erase s (fun i ↦ eLpNorm (f i) (p i) μ) hi₀
  -- If all exponents are finite, we're in the case covered by `ENNReal.lintegral_prod_norm_pow_le`
  have hf' : ∀ i ∈ s, AEMeasurable (fun a ↦ ((f i a) ^ (p i).toReal)) μ :=
    fun i hi ↦ (hf i hi).pow_const (p i).toReal
  have hp₁ : ∑ i ∈ s, (p i).toReal⁻¹ = 1 := by
    simp_rw [← (ENNReal.toReal_eq_one_iff 1).mpr rfl, ← ENNReal.toReal_inv]
    suffices (∑ x ∈ s, (p x)⁻¹).toReal = ∑ x ∈ s, (p x)⁻¹.toReal by rw [← this, hp]
    refine ENNReal.toReal_sum (fun i hi eq_top ↦ ?_)
    exact ENNReal.one_ne_top <| hp ▸ ENNReal.sum_eq_top.mpr ⟨i, hi, eq_top⟩
  have hp₂ : ∀ i ∈ s, 0 ≤ (p i).toReal⁻¹ := by intros; positivity
  have p_ne_0 : ∀ i ∈ s, p i ≠ 0 :=
    fun i hi eq0 ↦ one_ne_top <| hp.symm.trans <| ENNReal.sum_eq_top.mpr ⟨i, hi, by simp [eq0]⟩
  have p_ne_top : ∀ i ∈ s, p i ≠ ∞ := fun i hi h ↦ exists_top ⟨i, hi, h⟩
  convert ENNReal.lintegral_prod_norm_pow_le s hf' hp₁ hp₂ with a i₀ hi₀ i hi
  · rw [← ENNReal.rpow_mul, mul_inv_cancel₀, rpow_one]
    exact ENNReal.toReal_ne_zero.mpr ⟨p_ne_0 i₀ hi₀, (exists_top ⟨i₀, hi₀, ·⟩)⟩
  · simp [eLpNorm, eLpNorm', p_ne_0 i hi, p_ne_top i hi]

/-- **Hölder's inequality** for functions `α → ℝ≥0∞`, using exponents in `ℝ≥0∞` -/
theorem lintegral_mul_le_eLpNorm_mul_eLqNorm {p q : ℝ≥0∞} (hpq : p.HolderConjugate q)
    {f g : α → ENNReal} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    ∫⁻ (a : α), (f * g) a ∂μ ≤ eLpNorm f p μ * eLpNorm g q μ := by
  sorry

end ENNReal


section Convolution

open scoped Convolution

-- Used in the proof of Young's convolution inequality
private lemma r_sub_p_nonneg {p q r : ℝ} (p0 : 0 < p) (hq : 1 ≤ q) (r0 : 0 < r)
    (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) : 0 ≤ r - p := by
  rw [sub_nonneg, ← inv_le_inv₀ r0 p0, ← add_le_add_iff_right, hpqr]
  exact add_le_add_left ((inv_le_one₀ (lt_of_lt_of_le one_pos hq)).mpr hq) r⁻¹

namespace ENNReal

universe u𝕜 uG uE uE' uF

variable {𝕜 : Type u𝕜} {G : Type uG} [MeasurableSpace G] {μ : Measure G}
  {E : Type uE} {E' : Type uE'} {F : Type uF}

variable [NormedAddCommGroup E] [NormedAddCommGroup E'] [NormedAddCommGroup F]
  {f : G → E} {g : G → E'}

-- Used in the proof of `enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm`
open ENNReal in
private lemma eLpNorm_eq_eLpNorm_rpow (h : G → E) {r e : ℝ} (r0 : 0 < r) (e0 : 0 < e)
    (re0 : 0 ≤ r - e) (μ0 : μ ≠ 0) :
    eLpNorm (‖h ·‖ₑ ^ ((r - e) / r)) (ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e)) μ =
    eLpNorm h (ENNReal.ofReal e) μ ^ ((r - e) / r) := by
  have er_pos : 0 < e * r := _root_.mul_pos e0 r0
  by_cases exp_zero : 0 = r - e
  · simp [eLpNorm, eLpNorm', ← exp_zero, er_pos.not_le, eLpNormEssSup_const _ μ0]
  have r_sub_e_pos : 0 < r - e := lt_of_le_of_ne re0 exp_zero
  have lt_top : ENNReal.ofReal (e * r) / ENNReal.ofReal (r - e) < ∞ :=
    div_lt_top ofReal_ne_top <| (not_iff_not.mpr ofReal_eq_zero).mpr r_sub_e_pos.not_le
  simp only [eLpNorm, eLpNorm', reduceIte, div_eq_zero_iff, ofReal_eq_zero, ofReal_ne_top,
    lt_top.ne, er_pos.not_le, e0.not_le, or_self, enorm_eq_self, ← rpow_mul]
  congr
  · ext; congr; field_simp; ring
  · field_simp

variable [NontriviallyNormedField 𝕜]

variable [NormedSpace 𝕜 E] [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
variable {L : E →L[𝕜] E' →L[𝕜] F}

-- Used to handle trivial case `c ≤ 0` when proving versions of Young's convolution inequality
-- assuming `∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖)`
private theorem convolution_zero_of_c_nonpos [AddGroup G] {f : G → E} {g : G → E'} {c : ℝ}
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (hc : c ≤ 0) : f ⋆[L, μ] g = 0 := by
  have : ∀ (x y : G), L (f x) (g y) = 0 :=
    fun x y ↦ norm_le_zero_iff.mp <| (hL x y).trans <| mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg hc (norm_nonneg (f x))) (norm_nonneg (g y))
  unfold convolution
  simp only [this, integral_zero]
  rfl

-- Auxiliary inequality used to prove inequalities with simpler conditions on f and g.
private theorem eLpNorm_top_convolution_le_aux [AddCommGroup G] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable (‖f ·‖ₑ) μ)
    (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : ∀ x : G, eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  by_cases hc : c ≤ 0
  · simp [convolution_zero_of_c_nonpos hL hc]
  push_neg at hc
  rw [eLpNorm_exponent_top, eLpNormEssSup]
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall fun x ↦ ?_)
  apply le_trans <| enorm_integral_le_lintegral_enorm _
  calc ∫⁻ y, ‖(L (f y)) (g (x - y))‖ₑ ∂μ
    _ ≤ ∫⁻ y, ENNReal.ofReal c * ‖f y‖ₑ * ‖g (x - y)‖ₑ ∂μ := by
      simp_rw [← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul hc.le]
      refine lintegral_mono (fun y ↦ ?_)
      rw [← ENNReal.ofReal_mul <| mul_nonneg hc.le (norm_nonneg _)]
      exact ENNReal.ofReal_le_ofReal <| hL y (x - y)
    _ ≤ _ := by
      simp_rw [mul_assoc, lintegral_const_mul' _ _ ofReal_ne_top]
      simpa [hg' x] using mul_left_mono (ENNReal.lintegral_mul_le_eLpNorm_mul_eLqNorm hpq hf (hg x))

variable [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [BorelSpace G]
  [μ.IsAddHaarMeasure] [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  sorry

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le' {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (c : ℝ)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  sorry

-- Auxiliary inequality used to prove versions with simpler conditions on `f` and `g`
open ENNReal in
private theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (hf : AEMeasurable (‖f ·‖ₑ) μ) (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) := by
  sorry

open ENNReal in
/-- This inequality is used in the proof of Young's convolution inequality
`eLpNorm_convolution_le_ofReal`. See `enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm'` for
a version assuming a.e. strong measurability instead. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm [MeasurableSpace E]
    [OpensMeasurableSpace E] [MeasurableSpace E'] [OpensMeasurableSpace E'] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) :=
  enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux hp hq hr hpqr hf.enorm
    (fun x ↦ (hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x).enorm) c hL x

open ENNReal in
/-- This inequality is used in the proof of Young's convolution inequality
`eLpNorm_convolution_le_ofReal'`. -/
theorem enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm' {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) (x : G) :
    ‖(f ⋆[L, μ] g) x‖ₑ ≤
      .ofReal c * eLpNorm (fun y ↦ (‖f y‖ₑ ^ p * ‖g (x - y)‖ₑ ^ q) ^ (1 / r)) (.ofReal r) μ *
      ((eLpNorm f (.ofReal p) μ) ^ ((r - p) / r) *
      (eLpNorm g (.ofReal q) μ) ^ ((r - q) / r)) :=
  enorm_convolution_le_eLpNorm_mul_eLpNorm_mul_eLpNorm_aux hp hq hr hpqr hf.enorm
    (fun x ↦ (hg.comp_quasiMeasurePreserving <| quasiMeasurePreserving_sub_left μ x).enorm) c hL x

-- Auxiliary inequality used to prove versions with simpler conditions on `f` and `g`
private theorem eLpNorm_convolution_le_ofReal_aux {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1) {f : G → E} {g : G → E'}
    (hf : AEMeasurable (‖f ·‖ₑ) μ) (hg : ∀ x : G, AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : AEMeasurable (fun (x : G × G) ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q) (μ.prod μ))
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  sorry

theorem eLpNorm_convolution_le_ofReal [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  refine eLpNorm_convolution_le_ofReal_aux hp hq hr hpqr hf.enorm ?_ ?_ c hL
  · intro x; exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x) |>.enorm
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const q

theorem eLpNorm_convolution_le_ofReal' {p q r : ℝ}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) (.ofReal r) μ ≤
    .ofReal c * eLpNorm f (.ofReal p) μ * eLpNorm g (.ofReal q) μ := by
  refine eLpNorm_convolution_le_ofReal_aux hp hq hr hpqr hf.enorm ?_ ?_ c hL
  · intro x; exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left μ x) |>.enorm
  · exact hg.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub μ μ) |>.enorm.pow_const q

-- Auxiliary result to prove the following versions with simpler assumptions on `f` and `g`
private theorem eLpNorm_convolution_le_of_norm_le_mul_aux {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable (‖f ·‖ₑ) μ)
    (hg : ∀ (x : G), AEMeasurable (‖g <| x - ·‖ₑ) μ)
    (hg' : ∀ (x : G), eLpNorm (‖g <| x - ·‖ₑ) q μ = eLpNorm (‖g ·‖ₑ) q μ)
    (hg'' : AEMeasurable (fun x ↦ ‖(g ∘ fun p ↦ p.1 - p.2) x‖ₑ ^ q.toReal) (μ.prod μ))
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  -- First use `eLpNorm_top_convolution_le` to handle the cases where any exponent is `∞`
  by_cases r_top : r = ∞
  · rw [r_top, ENNReal.inv_top, zero_add] at hpqr
    have hpq : p.HolderConjugate q := holderConjugate_iff.mpr hpqr
    rw [r_top]
    refine eLpNorm_top_convolution_le_aux hpq hf hg hg' c hL
  have hpq : 1 < p⁻¹ + q⁻¹ := by
    rw [hpqr]
    nth_rewrite 1 [← zero_add 1]
    apply ENNReal.add_lt_add_right ENNReal.one_ne_top
    exact (zero_le r⁻¹).lt_or_eq.resolve_right (ENNReal.inv_ne_zero.mpr r_top).symm
  have p_ne_top : p ≠ ∞ := by contrapose! hq; simpa [hq] using hpq
  have q_ne_top : q ≠ ∞ := by contrapose! hp; simpa [hp] using hpq
  -- When all exponents are finite, apply `eLpNorm_convolution_le_ofReal`
  rw [← ENNReal.ofReal_toReal_eq_iff.mpr p_ne_top, ← ENNReal.ofReal_toReal_eq_iff.mpr q_ne_top,
    ← ENNReal.ofReal_toReal_eq_iff.mpr r_top]
  refine eLpNorm_convolution_le_ofReal_aux ?_ ?_ ?_ ?_ hf hg hg'' c hL; rotate_right
  · simp_rw [← ENNReal.toReal_one, ← ENNReal.toReal_inv]
    rw [← ENNReal.toReal_add _ ENNReal.one_ne_top, ← ENNReal.toReal_add, hpqr]
    all_goals exact ENNReal.inv_ne_top.mpr (fun h ↦ (h ▸ one_pos).not_le (by assumption))
  all_goals rwa [← ENNReal.toReal_one, ENNReal.toReal_le_toReal ENNReal.one_ne_top (by assumption)]

variable (L)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  sorry

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ` is replaced with a bound for `L` restricted to the ranges
of `f` and `g`; see `eLpNorm_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_convolution_le_of_norm_le_mul' {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ .ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  sorry

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEMeasurable f μ) (hg : AEMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

/-- **Young's convolution inequality**: the `L^r` seminorm of a convolution `(f ⋆[L, μ] g)` is
bounded by `‖L‖ₑ` times the product of the `L^p` and `L^q` seminorms, where
`1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_convolution_le_enorm_mul' {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : G → E} {g : G → E'} (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    eLpNorm (f ⋆[L, μ] g) r μ ≤ ‖L‖ₑ * eLpNorm f p μ * eLpNorm g q μ := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_convolution_le_of_norm_le_mul' L hp hq hr hpqr hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

open Set AddCircle in
/-- **Young's convolution inequality** on (a, a + T]: the `L^r` seminorm of the convolution
of `T`-periodic functions over (a, a + T] is bounded by `‖L‖ₑ` times the product of
the `L^p` and `L^q` seminorms on that interval, where `1 / p + 1 / q = 1 / r + 1`. Here `‖L‖ₑ`
is replaced with a  bound for `L` restricted to the ranges of `f` and `g`; see
`eLpNorm_Ioc_convolution_le_enorm_mul` for a version using `‖L‖ₑ` explicitly. -/
theorem eLpNorm_Ioc_convolution_le_of_norm_le_mul (a : ℝ) {T : ℝ} [hT : Fact (0 < T)]
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : ℝ → E} {g : ℝ → E'} (hfT : f.Periodic T) (hgT : g.Periodic T)
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g)
    (c : ℝ) (hL : ∀ (x y : ℝ), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm ((Ioc a (a + T)).indicator fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y))) r ≤
    .ofReal c * eLpNorm ((Ioc a (a + T)).indicator f) p * eLpNorm ((Ioc a (a + T)).indicator g) q :=
  sorry

open Set in
/-- **Young's convolution inequality** on (a, a + T]: the `L^r` seminorm of the convolution
of `T`-periodic functions over (a, a + T] is bounded by `‖L‖ₑ` times the product of
the `L^p` and `L^q` seminorms on that interval, where `1 / p + 1 / q = 1 / r + 1`. -/
theorem eLpNorm_Ioc_convolution_le_enorm_mul (a : ℝ) {T : ℝ} [hT : Fact (0 < T)]
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hr : 1 ≤ r) (hpqr : p⁻¹ + q⁻¹ = r⁻¹ + 1)
    {f : ℝ → E} {g : ℝ → E'} (hfT : f.Periodic T) (hgT : g.Periodic T)
    (hf : AEStronglyMeasurable f) (hg : AEStronglyMeasurable g) :
    eLpNorm ((Ioc a (a + T)).indicator fun x ↦ ∫ y in a..a+T, L (f y) (g (x - y))) r ≤
    ‖L‖ₑ * eLpNorm ((Ioc a (a + T)).indicator f) p * eLpNorm ((Ioc a (a + T)).indicator g) q := by
  rw [← enorm_norm, Real.enorm_of_nonneg (norm_nonneg L)]
  exact eLpNorm_Ioc_convolution_le_of_norm_le_mul L a hp hq hr hpqr hfT hgT hf hg ‖L‖ <| fun x y ↦
    ((L (f x)).le_opNorm (g y)).trans <| mul_le_mul_of_nonneg_right (L.le_opNorm _) (norm_nonneg _)

end ENNReal

end Convolution

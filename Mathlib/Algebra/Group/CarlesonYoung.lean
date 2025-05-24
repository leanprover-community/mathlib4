/-
Copyright (c) 2025
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.Analysis.Convolution

-- Copied from https://github.com/Aaron1011/carleson/blob/d7fa3e22cb1365ed36c23da4b8928023afc69d3b/Carleson/ToMathlib/MeasureTheory/Integral/MeanInequalities.lean
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

variable  [TopologicalSpace G] [BorelSpace G]
 [LocallyCompactSpace G] [SecondCountableTopology G]

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le [AddGroup G]  [IsTopologicalAddGroup G] [μ.IsAddHaarMeasure] [μ.IsNegInvariant] [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace E'] [OpensMeasurableSpace E'] {p q : ℝ≥0∞}
    (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'} (hf : AEMeasurable f μ)
    (hg : AEMeasurable g μ) (c : ℝ) (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  sorry

/-- Special case of **Young's convolution inequality** when `r = ∞`. -/
theorem eLpNorm_top_convolution_le' [AddGroup G]  [IsTopologicalAddGroup G] [μ.IsAddHaarMeasure] [μ.IsNegInvariant]  {p q : ℝ≥0∞} (hpq : p.HolderConjugate q) {f : G → E} {g : G → E'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) (c : ℝ)
    (hL : ∀ (x y : G), ‖L (f x) (g y)‖ ≤ c * ‖f x‖ * ‖g y‖) :
    eLpNorm (f ⋆[L, μ] g) ∞ μ ≤ ENNReal.ofReal c * eLpNorm f p μ * eLpNorm g q μ := by
  sorry

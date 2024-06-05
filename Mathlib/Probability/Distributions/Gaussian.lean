/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne, Alexander Bentkamp
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Probability.Notation
import Mathlib.MeasureTheory.Decomposition.Lebesgue

/-!
# Gaussian distributions over ℝ

We define a Gaussian measure over the reals.

## Main definitions

* `gaussianPDFReal`: the function `μ v x ↦ (1 / (sqrt (2 * pi * v))) * exp (- (x - μ)^2 / (2 * v))`,
  which is the probability density function of a Gaussian distribution with mean `μ` and
  variance `v` (when `v ≠ 0`).
* `gaussianPDF`: `ℝ≥0∞`-valued pdf, `gaussianPDF μ v x = ENNReal.ofReal (gaussianPDFReal μ v x)`.
* `gaussianReal`: a Gaussian measure on `ℝ`, parametrized by its mean `μ` and variance `v`.
  If `v = 0`, this is `dirac μ`, otherwise it is defined as the measure with density
  `gaussianPDF μ v` with respect to the Lebesgue measure.

## Main results

* `gaussianReal_add_const`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `X + y` is Gaussian with mean `μ + y` and variance `v`.
* `gaussianReal_const_mul`: if `X` is a random variable with Gaussian distribution with mean `μ` and
  variance `v`, then `c * X` is Gaussian with mean `c * μ` and variance `c^2 * v`.

-/

open scoped ENNReal NNReal Real

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

/-- Probability density function of the gaussian distribution with mean `μ` and variance `v`. -/
noncomputable
def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * rexp (- (x - μ)^2 / (2 * v))

lemma gaussianPDFReal_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDFReal μ v =
      fun x ↦ (Real.sqrt (2 * π * v))⁻¹ * rexp (- (x - μ)^2 / (2 * v)) := rfl

@[simp]
lemma gaussianPDFReal_zero_var (m : ℝ) : gaussianPDFReal m 0 = 0 := by
  ext1 x
  simp [gaussianPDFReal]

/-- The gaussian pdf is positive when the variance is not zero. -/
lemma gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The gaussian pdf is nonnegative. -/
lemma gaussianPDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The gaussian pdf is measurable. -/
lemma measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDFReal μ v) :=
  (((measurable_id.add_const _).pow_const _).neg.div_const _).exp.const_mul _

/-- The gaussian pdf is strongly measurable. -/
lemma stronglyMeasurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (gaussianPDFReal μ v) :=
  (measurable_gaussianPDFReal μ v).stronglyMeasurable

lemma integrable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : ℝ → ℝ := fun x ↦ (√(2 * π * v))⁻¹ * rexp (- x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x ↦ (√(2 * π * v))⁻¹ * rexp (- (2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simp [lt_of_le_of_ne (zero_le _) (Ne.symm hv)]
    ext x
    simp only [g, zero_lt_two, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field_simp
  exact Integrable.comp_sub_right hg μ

/-- The gaussian distribution pdf integrates to 1 when the variance is not zero.  -/
lemma lintegral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (gaussianPDFReal μ v x) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v) volume :=
    (stronglyMeasurable_gaussianPDFReal μ v).aestronglyMeasurable
  have hf : 0 ≤ₐₛ gaussianPDFReal μ v := ae_of_all _ (gaussianPDFReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal, zero_lt_two, mul_nonneg_iff_of_pos_right, one_div,
    Nat.cast_ofNat, integral_mul_left]
  rw [integral_sub_right_eq_self (μ := volume) (fun a ↦ rexp (-a ^ 2 / ((2 : ℝ) * v))) μ]
  simp only [zero_lt_two, mul_nonneg_iff_of_pos_right, div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [← neg_mul]
  rw [neg_mul, integral_gaussian, ← Real.sqrt_inv, ← Real.sqrt_mul]
  · field_simp
    ring
  · positivity

/-- The gaussian distribution pdf integrates to 1 when the variance is not zero.  -/
lemma integral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∫ x, gaussianPDFReal μ v x = 1 := by
  have h := lintegral_gaussianPDFReal_eq_one μ hv
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_gaussianPDFReal _ _)
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)), ← ENNReal.ofReal_one] at h
  rwa [← ENNReal.ofReal_eq_ofReal_iff (integral_nonneg (gaussianPDFReal_nonneg _ _)) zero_le_one]

lemma gaussianPDFReal_sub {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPDFReal μ v (x - y) = gaussianPDFReal (μ + y) v x := by
  simp only [gaussianPDFReal]
  rw [sub_add_eq_sub_sub_swap]

lemma gaussianPDFReal_add {μ : ℝ} {v : ℝ≥0} (x y : ℝ) :
    gaussianPDFReal μ v (x + y) = gaussianPDFReal (μ - y) v x := by
  rw [sub_eq_add_neg, ← gaussianPDFReal_sub, sub_eq_add_neg, neg_neg]

lemma gaussianPDFReal_inv_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v (c⁻¹ * x) = |c| * gaussianPDFReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) x := by
  simp only [gaussianPDFReal.eq_1, zero_lt_two, mul_nonneg_iff_of_pos_left, NNReal.zero_le_coe,
    Real.sqrt_mul', one_div, mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk, NNReal.coe_pos]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · field_simp
    rw [Real.sqrt_sq_eq_abs]
    ring_nf
    calc (Real.sqrt ↑v)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt π)⁻¹
      = (Real.sqrt ↑v)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt π)⁻¹ * (|c| * |c|⁻¹) := by
          rw [mul_inv_cancel, mul_one]
          simp only [ne_eq, abs_eq_zero, hc, not_false_eq_true]
    _ = (Real.sqrt ↑v)⁻¹ * (Real.sqrt 2)⁻¹ * (Real.sqrt π)⁻¹ * |c| * |c|⁻¹ := by ring
  · congr 1
    field_simp
    congr 1
    ring

lemma gaussianPDFReal_mul {μ : ℝ} {v : ℝ≥0} {c : ℝ} (hc : c ≠ 0) (x : ℝ) :
    gaussianPDFReal μ v (c * x)
      = |c⁻¹| * gaussianPDFReal (c⁻¹ * μ) (⟨(c^2)⁻¹, inv_nonneg.mpr (sq_nonneg _)⟩ * v) x := by
  conv_lhs => rw [← inv_inv c, gaussianPDFReal_inv_mul (inv_ne_zero hc)]
  simp

/-- The pdf of a Gaussian distribution on ℝ with mean `μ` and variance `v`. -/
noncomputable
def gaussianPDF (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ≥0∞ := ENNReal.ofReal (gaussianPDFReal μ v x)

lemma gaussianPDF_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDF μ v = fun x ↦ ENNReal.ofReal (gaussianPDFReal μ v x) := rfl

@[simp]
lemma gaussianPDF_zero_var (μ : ℝ) : gaussianPDF μ 0 = 0 := by
  ext
  simp [gaussianPDF]

lemma gaussianPDF_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 < gaussianPDF μ v x := by
  rw [gaussianPDF, ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ _ _ hv

@[measurability]
lemma measurable_gaussianPDF (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDF μ v) :=
  (measurable_gaussianPDFReal _ _).ennreal_ofReal

@[simp]
lemma lintegral_gaussianPDF_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, gaussianPDF μ v x = 1 :=
  lintegral_gaussianPDFReal_eq_one μ h

end GaussianPDF

section GaussianReal

/-- A Gaussian distribution on `ℝ` with mean `μ` and variance `v`. -/
noncomputable
def gaussianReal (μ : ℝ) (v : ℝ≥0) : Measure ℝ :=
  if v = 0 then Measure.dirac μ else volume.withDensity (gaussianPDF μ v)

lemma gaussianReal_of_var_ne_zero (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v = volume.withDensity (gaussianPDF μ v) := if_neg hv

@[simp]
lemma gaussianReal_zero_var (μ : ℝ) : gaussianReal μ 0 = Measure.dirac μ := if_pos rfl

instance instIsProbabilityMeasureGaussianReal (μ : ℝ) (v : ℝ≥0) :
    IsProbabilityMeasure (gaussianReal μ v) where
  measure_univ := by by_cases h : v = 0 <;> simp [gaussianReal_of_var_ne_zero, h]

lemma gaussianReal_apply (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ∫⁻ x in s, gaussianPDF μ v x := by
  rw [gaussianReal_of_var_ne_zero _ hv, withDensity_apply' _ s]

lemma gaussianReal_apply_eq_integral (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s = ENNReal.ofReal (∫ x in s, gaussianPDFReal μ v x) := by
  rw [gaussianReal_apply _ hv s, ofReal_integral_eq_lintegral_ofReal]
  · rfl
  · exact (integrable_gaussianPDFReal _ _).restrict
  · exact ae_of_all _ (gaussianPDFReal_nonneg _ _)

lemma gaussianReal_absolutelyContinuous (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal μ v ≪ volume := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  exact withDensity_absolutelyContinuous _ _

lemma gaussianReal_absolutelyContinuous' (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    volume ≪ gaussianReal μ v := by
  rw [gaussianReal_of_var_ne_zero _ hv]
  refine withDensity_absolutelyContinuous' ?_ ?_
  · exact (measurable_gaussianPDF _ _).aemeasurable
  · exact ae_of_all _ (fun _ ↦ (gaussianPDF_pos _ hv _).ne')

lemma rnDeriv_gaussianReal (μ : ℝ) (v : ℝ≥0) :
    ∂(gaussianReal μ v)/∂volume =ₐₛ gaussianPDF μ v := by
  by_cases hv : v = 0
  · simp only [hv, gaussianReal_zero_var, gaussianPDF_zero_var]
    refine (Measure.eq_rnDeriv measurable_zero (mutuallySingular_dirac μ volume) ?_).symm
    rw [withDensity_zero, add_zero]
  · rw [gaussianReal_of_var_ne_zero _ hv]
    exact Measure.rnDeriv_withDensity _ (measurable_gaussianPDF μ v)

section Transformations

variable {μ : ℝ} {v : ℝ≥0}

lemma _root_.MeasurableEmbedding.gaussianReal_comap_apply (hv : v ≠ 0)
    {f : ℝ → ℝ} (hf : MeasurableEmbedding f)
    {f' : ℝ → ℝ} (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).comap f s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]
  exact hf.withDensity_ofReal_comap_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

lemma _root_.MeasurableEquiv.gaussianReal_map_symm_apply (hv : v ≠ 0) (f : ℝ ≃ᵐ ℝ) {f' : ℝ → ℝ}
    (h_deriv : ∀ x, HasDerivAt f (f' x) x) {s : Set ℝ} (hs : MeasurableSet s) :
    (gaussianReal μ v).map f.symm s
      = ENNReal.ofReal (∫ x in s, |f' x| * gaussianPDFReal μ v (f x)) := by
  rw [gaussianReal_of_var_ne_zero _ hv, gaussianPDF_def]
  exact f.withDensity_ofReal_map_symm_apply_eq_integral_abs_deriv_mul' hs h_deriv
    (ae_of_all _ (gaussianPDFReal_nonneg _ _)) (integrable_gaussianPDFReal _ _)

/-- The map of a Gaussian distribution by addition of a constant is a Gaussian. -/
lemma gaussianReal_map_add_const (y : ℝ) :
    (gaussianReal μ v).map (· + y) = gaussianReal (μ + y) v := by
  by_cases hv : v = 0
  · simp only [hv, ne_eq, not_true, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.add_const _) _
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_neg, abs_one, MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, one_mul, ne_eq]
  rw [gaussianReal_apply_eq_integral _ hv s']
  simp [e, gaussianPDFReal_sub _ y, Homeomorph.addRight, ← sub_eq_add_neg]

/-- The map of a Gaussian distribution by addition of a constant is a Gaussian. -/
lemma gaussianReal_map_const_add (y : ℝ) :
    (gaussianReal μ v).map (y + ·) = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_map_add_const y

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
lemma gaussianReal_map_const_mul (c : ℝ) :
    (gaussianReal μ v).map (c * ·) = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  by_cases hv : v = 0
  · simp only [hv, mul_zero, ne_eq, not_true, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.const_mul c) μ
  by_cases hc : c = 0
  · simp only [hc, zero_mul, ne_eq, abs_zero, mul_eq_zero]
    rw [Measure.map_const]
    simp only [ne_eq, measure_univ, one_smul, mul_eq_zero]
    convert (gaussianReal_zero_var 0).symm
    simp only [ne_eq, zero_pow, mul_eq_zero, hv, or_false, not_false_eq_true]
    rfl
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [MeasurableEquiv.coe_mk, Equiv.coe_fn_mk, ne_eq, mul_eq_zero]
  rw [gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀, Equiv.toFun_as_coe, Equiv.mulLeft₀_apply, Equiv.invFun_as_coe,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    Equiv.coe_fn_symm_mk, gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel]
  rwa [ne_eq, abs_eq_zero]

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
lemma gaussianReal_map_mul_const (c : ℝ) :
    (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

variable {Ω : Type} [MeasureSpace Ω]

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X + y`
has Gaussian law with mean `μ + y` and variance `v`. -/
lemma gaussianReal_add_const {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ X ω + y) ℙ = gaussianReal (μ + y) v := by
  have hXm : AEMeasurable X := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ ω + y) ∘ X) ℙ = gaussianReal (μ + y) v
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.add_const _).aemeasurable hXm, hX,
    gaussianReal_map_add_const y]

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `y + X`
has Gaussian law with mean `μ + y` and variance `v`. -/
lemma gaussianReal_const_add {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (y : ℝ) :
    Measure.map (fun ω ↦ y + X ω) ℙ = gaussianReal (μ + y) v := by
  simp_rw [add_comm y]
  exact gaussianReal_add_const hX y

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `c * X`
has Gaussian law with mean `c * μ` and variance `c^2 * v`. -/
lemma gaussianReal_const_mul {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (c : ℝ) :
    Measure.map (fun ω ↦ c * X ω) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  have hXm : AEMeasurable X := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  change Measure.map ((fun ω ↦ c * ω) ∘ X) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  rw [← AEMeasurable.map_map_of_aemeasurable (measurable_id'.const_mul c).aemeasurable hXm, hX]
  exact gaussianReal_map_const_mul c

/-- If `X` is a real random variable with Gaussian law with mean `μ` and variance `v`, then `X * c`
has Gaussian law with mean `c * μ` and variance `c^2 * v`. -/
lemma gaussianReal_mul_const {X : Ω → ℝ} (hX : Measure.map X ℙ = gaussianReal μ v) (c : ℝ) :
    Measure.map (fun ω ↦ X ω * c) ℙ = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_const_mul hX c

end Transformations

end GaussianReal

end ProbabilityTheory

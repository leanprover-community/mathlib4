/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Luccioli, Rémy Degenne, Alexander Bentkamp
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Group.Convolution
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Probability.Independence.Basic

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

open scoped ENNReal NNReal Real Complex

open MeasureTheory

namespace ProbabilityTheory

section GaussianPDF

/-- Probability density function of the Gaussian distribution with mean `μ` and variance `v`. -/
noncomputable
def gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) : ℝ :=
  (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v))

lemma gaussianPDFReal_def (μ : ℝ) (v : ℝ≥0) :
    gaussianPDFReal μ v =
      fun x ↦ (√(2 * π * v))⁻¹ * rexp (-(x - μ) ^ 2 / (2 * v)) := rfl

@[simp]
lemma gaussianPDFReal_zero_var (m : ℝ) : gaussianPDFReal m 0 = 0 := by
  ext1 x
  simp [gaussianPDFReal]

/-- The Gaussian pdf is positive when the variance is not zero. -/
lemma gaussianPDFReal_pos (μ : ℝ) (v : ℝ≥0) (x : ℝ) (hv : v ≠ 0) : 0 < gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The Gaussian pdf is nonnegative. -/
lemma gaussianPDFReal_nonneg (μ : ℝ) (v : ℝ≥0) (x : ℝ) : 0 ≤ gaussianPDFReal μ v x := by
  rw [gaussianPDFReal]
  positivity

/-- The Gaussian pdf is measurable. -/
@[fun_prop]
lemma measurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) : Measurable (gaussianPDFReal μ v) :=
  (((measurable_id.add_const _).pow_const _).neg.div_const _).exp.const_mul _

/-- The Gaussian pdf is strongly measurable. -/
@[fun_prop]
lemma stronglyMeasurable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    StronglyMeasurable (gaussianPDFReal μ v) :=
  (measurable_gaussianPDFReal μ v).stronglyMeasurable

@[fun_prop]
lemma integrable_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) :
    Integrable (gaussianPDFReal μ v) := by
  rw [gaussianPDFReal_def]
  by_cases hv : v = 0
  · simp [hv]
  let g : ℝ → ℝ := fun x ↦ (√(2 * π * v))⁻¹ * rexp (-x ^ 2 / (2 * v))
  have hg : Integrable g := by
    suffices g = fun x ↦ (√(2 * π * v))⁻¹ * rexp (-(2 * v)⁻¹ * x ^ 2) by
      rw [this]
      refine (integrable_exp_neg_mul_sq ?_).const_mul (√(2 * π * v))⁻¹
      simp [lt_of_le_of_ne (zero_le _) (Ne.symm hv)]
    ext x
    simp only [g, NNReal.zero_le_coe, Real.sqrt_mul',
      mul_inv_rev, NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_ofNat, neg_mul, mul_eq_mul_left_iff,
      Real.exp_eq_exp, mul_eq_zero, inv_eq_zero, Real.sqrt_eq_zero, NNReal.coe_eq_zero, hv,
      false_or]
    rw [mul_comm]
    left
    field_simp
  exact Integrable.comp_sub_right hg μ

/-- The Gaussian distribution pdf integrates to 1 when the variance is not zero. -/
lemma lintegral_gaussianPDFReal_eq_one (μ : ℝ) {v : ℝ≥0} (h : v ≠ 0) :
    ∫⁻ x, ENNReal.ofReal (gaussianPDFReal μ v x) = 1 := by
  rw [← ENNReal.toReal_eq_one_iff]
  have hfm : AEStronglyMeasurable (gaussianPDFReal μ v) volume := by fun_prop
  have hf : 0 ≤ₐₛ gaussianPDFReal μ v := ae_of_all _ (gaussianPDFReal_nonneg μ v)
  rw [← integral_eq_lintegral_of_nonneg_ae hf hfm]
  simp only [gaussianPDFReal,
    integral_const_mul]
  rw [integral_sub_right_eq_self (μ := volume) (fun a ↦ rexp (-a ^ 2 / ((2 : ℝ) * v))) μ]
  simp only [div_eq_inv_mul, mul_inv_rev,
    mul_neg]
  simp_rw [← neg_mul]
  rw [neg_mul, integral_gaussian, ← Real.sqrt_inv, ← Real.sqrt_mul]
  · simp [field]
  · positivity

/-- The Gaussian distribution pdf integrates to 1 when the variance is not zero. -/
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
  simp only [gaussianPDFReal.eq_1, NNReal.zero_le_coe,
    Real.sqrt_mul', mul_inv_rev, NNReal.coe_mul, NNReal.coe_mk]
  rw [← mul_assoc]
  refine congr_arg₂ _ ?_ ?_
  · simp (disch := positivity) only [Real.sqrt_mul, mul_inv_rev, field]
    rw [Real.sqrt_sq_eq_abs]
  · congr 1
    field_simp

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
lemma gaussianPDF_zero_var (μ : ℝ) : gaussianPDF μ 0 = 0 := by ext; simp [gaussianPDF]

@[simp]
lemma toReal_gaussianPDF {μ : ℝ} {v : ℝ≥0} (x : ℝ) :
    (gaussianPDF μ v x).toReal = gaussianPDFReal μ v x := by
  rw [gaussianPDF, ENNReal.toReal_ofReal (gaussianPDFReal_nonneg μ v x)]

lemma gaussianPDF_pos (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x : ℝ) : 0 < gaussianPDF μ v x := by
  rw [gaussianPDF, ENNReal.ofReal_pos]
  exact gaussianPDFReal_pos _ _ _ hv

lemma gaussianPDF_lt_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : gaussianPDF μ v x < ∞ := by simp [gaussianPDF]

lemma gaussianPDF_ne_top {μ : ℝ} {v : ℝ≥0} {x : ℝ} : gaussianPDF μ v x ≠ ∞ := by simp [gaussianPDF]

@[simp]
lemma support_gaussianPDF {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) :
    Function.support (gaussianPDF μ v) = Set.univ := by
  ext x
  simp only [Set.mem_univ, iff_true]
  exact (gaussianPDF_pos _ hv x).ne'

@[measurability, fun_prop]
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

lemma noAtoms_gaussianReal {μ : ℝ} {v : ℝ≥0} (h : v ≠ 0) : NoAtoms (gaussianReal μ v) := by
  rw [gaussianReal_of_var_ne_zero _ h]
  infer_instance

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

lemma integral_gaussianReal_eq_integral_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {μ : ℝ} {v : ℝ≥0} {f : ℝ → E} (hv : v ≠ 0) :
    ∫ x, f x ∂(gaussianReal μ v) = ∫ x, gaussianPDFReal μ v x • f x := by
  simp [gaussianReal, hv,
    integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF _ _)
      (ae_of_all _ fun _ ↦ gaussianPDF_lt_top)]

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
  · simp only [hv, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.add_const _) _
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.addRight y).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ 1) x) x := fun _ ↦ (hasDerivAt_id _).sub_const y
  change (gaussianReal μ v).map e.symm = gaussianReal (μ + y) v
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs']
  simp only [abs_one, one_mul]
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
  · simp only [hv, mul_zero, gaussianReal_zero_var]
    exact Measure.map_dirac (measurable_id'.const_mul c) μ
  by_cases hc : c = 0
  · simp only [hc, zero_mul]
    rw [Measure.map_const]
    simp only [measure_univ, one_smul]
    convert (gaussianReal_zero_var 0).symm
    simp only [ne_eq, zero_pow, mul_eq_zero, hv, or_false, not_false_eq_true, reduceCtorEq,
      NNReal.mk_zero]
  let e : ℝ ≃ᵐ ℝ := (Homeomorph.mulLeft₀ c hc).symm.toMeasurableEquiv
  have he' : ∀ x, HasDerivAt e ((fun _ ↦ c⁻¹) x) x := by
    suffices ∀ x, HasDerivAt (fun x => c⁻¹ * x) (c⁻¹ * 1) x by rwa [mul_one] at this
    exact fun _ ↦ HasDerivAt.const_mul _ (hasDerivAt_id _)
  change (gaussianReal μ v).map e.symm = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v)
  ext s' hs'
  rw [MeasurableEquiv.gaussianReal_map_symm_apply hv e he' hs',
    gaussianReal_apply_eq_integral _ _ s']
  swap
  · simp only [ne_eq, mul_eq_zero, hv, or_false]
    rw [← NNReal.coe_inj]
    simp [hc]
  simp only [e, Homeomorph.mulLeft₀,
    Equiv.mulLeft₀_symm_apply, Homeomorph.toMeasurableEquiv_coe, Homeomorph.homeomorph_mk_coe_symm,
    gaussianPDFReal_inv_mul hc]
  congr with x
  suffices |c⁻¹| * |c| = 1 by rw [← mul_assoc, this, one_mul]
  rw [abs_inv, inv_mul_cancel₀]
  rwa [ne_eq, abs_eq_zero]

/-- The map of a Gaussian distribution by multiplication by a constant is a Gaussian. -/
lemma gaussianReal_map_mul_const (c : ℝ) :
    (gaussianReal μ v).map (· * c) = gaussianReal (c * μ) (⟨c^2, sq_nonneg _⟩ * v) := by
  simp_rw [mul_comm _ c]
  exact gaussianReal_map_const_mul c

lemma gaussianReal_map_neg : (gaussianReal μ v).map (fun x ↦ -x) = gaussianReal (-μ) v := by
  simpa using gaussianReal_map_const_mul (μ := μ) (v := v) (-1)

lemma gaussianReal_map_sub_const (y : ℝ) :
    (gaussianReal μ v).map (· - y) = gaussianReal (μ - y) v := by
  simp_rw [sub_eq_add_neg, gaussianReal_map_add_const]

lemma gaussianReal_map_const_sub (y : ℝ) :
    (gaussianReal μ v).map (y - ·) = gaussianReal (y - μ) v := by
  simp_rw [sub_eq_add_neg]
  have : (fun x ↦ y + -x) = (fun x ↦ y + x) ∘ fun x ↦ -x := by ext; simp
  rw [this, ← Measure.map_map (by fun_prop) (by fun_prop), gaussianReal_map_neg,
    gaussianReal_map_const_add, add_comm]

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

section CharacteristicFunction

open Real Complex

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {p : Measure Ω} {μ : ℝ} {v : ℝ≥0} {X : Ω → ℝ}

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The complex moment-generating function of a Gaussian distribution with mean `μ` and variance `v`
is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`. -/
theorem complexMGF_id_gaussianReal (z : ℂ) :
    complexMGF id (gaussianReal μ v) z = cexp (z * μ + v * z ^ 2 / 2) := by
  by_cases hv : v = 0
  · simp [complexMGF, hv]
  calc ∫ x, cexp (z * x) ∂gaussianReal μ v
    _ = ∫ x, gaussianPDFReal μ v x * cexp (z * x) ∂ℙ := by
      simp_rw [integral_gaussianReal_eq_integral_smul hv, Complex.real_smul]
    _ = (√(2 * π * v))⁻¹
        * ∫ x : ℝ, cexp (-(2 * v)⁻¹ * x ^ 2 + (z + μ / v) * x + -μ ^ 2 / (2 * v)) ∂ℙ := by
      unfold gaussianPDFReal
      push_cast
      simp_rw [mul_assoc, integral_const_mul, ← Complex.exp_add]
      congr with x
      congr 1
      ring
    _ = (√(2 * π * v))⁻¹ * (π / - -(2 * v)⁻¹) ^ (1 / 2 : ℂ)
        * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      rw [integral_cexp_quadratic (by simpa using pos_iff_ne_zero.mpr hv), ← mul_assoc]
    _ = 1 * cexp (-μ ^ 2 / (2 * v) - (z + μ / v) ^ 2 / (4 * -(2 * v)⁻¹)) := by
      congr 1
      simp only [field, sqrt_eq_rpow, one_div, ofReal_inv, NNReal.coe_inv, NNReal.coe_mul,
        NNReal.coe_ofNat, ofReal_mul, ofReal_ofNat, neg_neg, div_inv_eq_mul,
        ne_eq, ofReal_eq_zero, rpow_eq_zero, not_false_eq_true]
      rw [Complex.ofReal_cpow (by positivity)]
      push_cast
      ring_nf
    _ = cexp (z * μ + v * z ^ 2 / 2) := by
      rw [one_mul]
      congr 1
      have : (v : ℂ) ≠ 0 := by simpa
      simp [field]
      ring

/-- The complex moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `z ↦ exp (z * μ + v * z ^ 2 / 2)`. -/
theorem complexMGF_gaussianReal (hX : p.map X = gaussianReal μ v) (z : ℂ) :
    complexMGF X p z = cexp (z * μ + v * z ^ 2 / 2) := by
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← complexMGF_id_map hX_meas, hX, complexMGF_id_gaussianReal]

/-- The characteristic function of a Gaussian distribution with mean `μ` and variance `v`
is given by `t ↦ exp (t * μ - v * t ^ 2 / 2)`. -/
theorem charFun_gaussianReal (t : ℝ) :
    charFun (gaussianReal μ v) t = cexp (t * μ * I - v * t ^ 2 / 2) := by
  rw [← complexMGF_id_mul_I, complexMGF_id_gaussianReal]
  congr
  simp only [mul_pow, I_sq, mul_neg, mul_one, sub_eq_add_neg]
  ring_nf

/-- The moment-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ exp (μ * t + v * t ^ 2 / 2)`. -/
theorem mgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : ℝ) :
    mgf X p t = rexp (μ * t + v * t ^ 2 / 2) := by
  suffices (mgf X p t : ℂ) = rexp (μ * t + ↑v * t ^ 2 / 2) from mod_cast this
  have hX_meas : AEMeasurable X p := aemeasurable_of_map_neZero (by rw [hX]; infer_instance)
  rw [← mgf_id_map hX_meas, ← complexMGF_ofReal, hX, complexMGF_id_gaussianReal, mul_comm μ]
  norm_cast

theorem mgf_fun_id_gaussianReal :
    mgf (fun x ↦ x) (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) := by
  ext t
  rw [mgf_gaussianReal]
  simp

theorem mgf_id_gaussianReal : mgf id (gaussianReal μ v) = fun t ↦ rexp (μ * t + v * t ^ 2 / 2) :=
  mgf_fun_id_gaussianReal

/-- The cumulant-generating function of a random variable with Gaussian distribution
with mean `μ` and variance `v` is given by `t ↦ μ * t + v * t ^ 2 / 2`. -/
theorem cgf_gaussianReal (hX : p.map X = gaussianReal μ v) (t : ℝ) :
    cgf X p t = μ * t + v * t ^ 2 / 2 := by
  rw [cgf, mgf_gaussianReal hX t, Real.log_exp]

lemma integrable_exp_mul_gaussianReal (t : ℝ) :
    Integrable (fun x ↦ rexp (t * x)) (gaussianReal μ v) := by
  rw [← mgf_pos_iff, mgf_gaussianReal (μ := μ) (v := v) (by simp)]
  exact Real.exp_pos _

@[simp]
lemma integrableExpSet_id_gaussianReal : integrableExpSet id (gaussianReal μ v) = Set.univ := by
  ext
  simpa [integrableExpSet] using integrable_exp_mul_gaussianReal _

@[simp]
lemma integrableExpSet_fun_id_gaussianReal :
    integrableExpSet (fun x ↦ x) (gaussianReal μ v) = Set.univ :=
  integrableExpSet_id_gaussianReal

end CharacteristicFunction

section Moments

variable {μ : ℝ} {v : ℝ≥0}

/-- The mean of a real Gaussian distribution `gaussianReal μ v` is its mean parameter `μ`. -/
@[simp]
lemma integral_id_gaussianReal : ∫ x, x ∂gaussianReal μ v = μ := by
  rw [← deriv_mgf_zero (by simp), mgf_fun_id_gaussianReal, _root_.deriv_exp (by fun_prop)]
  simp only [mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div,
    add_zero, Real.exp_zero, one_mul]
  rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_fun_id_gaussianReal : Var[fun x ↦ x; gaussianReal μ v] = v := by
  rw [variance_eq_integral measurable_id'.aemeasurable]
  simp only [integral_id_gaussianReal]
  calc ∫ ω, (ω - μ) ^ 2 ∂gaussianReal μ v
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal μ v).map (fun x ↦ x - μ) := by
    rw [integral_map (by fun_prop) (by fun_prop)]
  _ = ∫ ω, ω ^ 2 ∂(gaussianReal 0 v) := by simp [gaussianReal_map_sub_const]
  _ = iteratedDeriv 2 (mgf (fun x ↦ x) (gaussianReal 0 v)) 0 := by
    rw [iteratedDeriv_mgf_zero] <;> simp
  _ = v := by
    rw [mgf_fun_id_gaussianReal, iteratedDeriv_succ, iteratedDeriv_one]
    simp only [zero_mul, zero_add]
    have : deriv (fun t ↦ rexp (v * t ^ 2 / 2)) = fun t ↦ v * t * rexp (v * t ^ 2 / 2) := by
      ext t
      rw [_root_.deriv_exp (by fun_prop)]
      simp only [deriv_div_const, differentiableAt_const, differentiableAt_fun_id, Nat.cast_ofNat,
        DifferentiableAt.fun_pow, deriv_fun_mul, deriv_const', zero_mul, deriv_fun_pow,
        Nat.add_one_sub_one, pow_one, deriv_id'', mul_one, zero_add]
      ring
    rw [this, deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_mul (by fun_prop) (by fun_prop)]
    simp

/-- The variance of a real Gaussian distribution `gaussianReal μ v` is
its variance parameter `v`. -/
@[simp]
lemma variance_id_gaussianReal : Var[id; gaussianReal μ v] = v :=
  variance_fun_id_gaussianReal

/-- All the moments of a real Gaussian distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_gaussianReal (p : ℝ≥0) : MemLp id p (gaussianReal μ v) :=
  memLp_of_mem_interior_integrableExpSet (by simp) p

/-- All the moments of a real Gaussian distribution are finite. That is, the identity is in Lp for
all finite `p`. -/
lemma memLp_id_gaussianReal' (p : ℝ≥0∞) (hp : p ≠ ∞) : MemLp id p (gaussianReal μ v) := by
  lift p to ℝ≥0 using hp
  exact memLp_id_gaussianReal p

end Moments

/-- Two real Gaussian distributions are equal iff they have the same mean and variance. -/
lemma gaussianReal_ext_iff {μ₁ μ₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    gaussianReal μ₁ v₁ = gaussianReal μ₂ v₂ ↔ μ₁ = μ₂ ∧ v₁ = v₂ := by
  refine ⟨fun h ↦ ?_, by rintro ⟨rfl, rfl⟩; rfl⟩
  rw [← integral_id_gaussianReal (μ := μ₁) (v := v₁),
    ← integral_id_gaussianReal (μ := μ₂) (v := v₂), h]
  simp only [integral_id_gaussianReal, true_and]
  suffices (v₁ : ℝ) = v₂ by simpa
  rw [← variance_id_gaussianReal (μ := μ₁) (v := v₁),
    ← variance_id_gaussianReal (μ := μ₂) (v := v₂), h]

section LinearMap

variable {μ : ℝ} {v : ℝ≥0}

lemma gaussianReal_map_linearMap (L : ℝ →ₗ[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) := by
  have : (L : ℝ → ℝ) = fun x ↦ L 1 * x := by
    ext x
    have : x = x • 1 := by simp
    conv_lhs => rw [this, L.map_smul, smul_eq_mul, mul_comm]
  rw [this, gaussianReal_map_const_mul]
  congr
  simp only [mul_one, left_eq_sup]
  positivity

lemma gaussianReal_map_continuousLinearMap (L : ℝ →L[ℝ] ℝ) :
    (gaussianReal μ v).map L = gaussianReal (L μ) ((L 1 ^ 2).toNNReal * v) :=
  gaussianReal_map_linearMap L

@[simp]
lemma integral_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := by
  have : ∫ x, L x ∂(gaussianReal μ v) = ∫ x, x ∂((gaussianReal μ v).map L) := by
    rw [integral_map (φ := L) (by fun_prop) (by fun_prop)]
  simp [this, gaussianReal_map_linearMap]

@[simp]
lemma integral_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    ∫ x, L x ∂(gaussianReal μ v) = L μ := integral_linearMap_gaussianReal L

@[simp]
lemma variance_linearMap_gaussianReal (L : ℝ →ₗ[ℝ] ℝ) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v := by
  rw [← variance_id_map, gaussianReal_map_linearMap, variance_id_gaussianReal]
  · simp only [NNReal.coe_mul, Real.coe_toNNReal']
  · fun_prop

@[simp]
lemma variance_continuousLinearMap_gaussianReal (L : ℝ →L[ℝ] ℝ) :
    Var[L; gaussianReal μ v] = (L 1 ^ 2).toNNReal * v :=
  variance_linearMap_gaussianReal L

end LinearMap

/-- The convolution of two real Gaussian distributions with means `m₁, m₂` and variances `v₁, v₂`
is a real Gaussian distribution with mean `m₁ + m₂` and variance `v₁ + v₂`. -/
lemma gaussianReal_conv_gaussianReal {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} :
    (gaussianReal m₁ v₁) ∗ (gaussianReal m₂ v₂) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  refine Measure.ext_of_charFun ?_
  ext t
  simp_rw [charFun_conv, charFun_gaussianReal]
  rw [← Complex.exp_add]
  simp only [Complex.ofReal_add, NNReal.coe_add]
  ring_nf

/- The sum of two real Gaussian variables with means `m₁, m₂` and variances `v₁, v₂` is a real
Gaussian distribution with mean `m₁ + m₂` and variance `v_1 + v_2`. -/
lemma gaussianReal_add_gaussianReal_of_indepFun {Ω} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {m₁ m₂ : ℝ} {v₁ v₂ : ℝ≥0} {X Y : Ω → ℝ} (hXY : IndepFun X Y P)
    (hX : P.map X = gaussianReal m₁ v₁) (hY : P.map Y = gaussianReal m₂ v₂) :
    P.map (X + Y) = gaussianReal (m₁ + m₂) (v₁ + v₂) := by
  rw [hXY.map_add_eq_map_conv_map₀', hX, hY, gaussianReal_conv_gaussianReal]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hX]
  · apply AEMeasurable.of_map_ne_zero; simp [NeZero.ne, hY]
  · rw [hX]; apply IsFiniteMeasure.toSigmaFinite
  · rw [hY]; apply IsFiniteMeasure.toSigmaFinite

end GaussianReal

end ProbabilityTheory

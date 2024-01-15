/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Fourier.FourierTransform
/-!
# Derivative of the Fourier transform

In this file we compute the Fréchet derivative of `𝓕 f`, where `f` is a function such that both
`f` and `v ↦ ‖v‖ * ‖f v‖` are integrable. Here `𝓕` is understood as an operator `(V → E) → (W → E)`,
where `V` and `W` are normed `ℝ`-vector spaces and the Fourier transform is taken with respect to a
continuous `ℝ`-bilinear pairing `L : V × W → ℝ`.

We also give a separate lemma for the most common case when `V = W = ℝ` and `L` is the obvious
multiplication map.
-/

noncomputable section

open Real Complex MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology

section SmulRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

lemma aestronglyMeasurable_smulRight {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] [NormedAddCommGroup B] [NormedSpace 𝕜 B]
    {f : X → A →L[𝕜] 𝕜} {g : X → B}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x : X ↦ (f x).smulRight (g x)) μ :=
  (ContinuousLinearMap.smulRightL 𝕜 A B).continuous₂.comp_aestronglyMeasurable (hf.prod_mk hg)

end SmulRight

section bilinear_maps

variable {𝕜 V W E : Type*} [NormedField 𝕜] [AddCommMonoid V] [TopologicalSpace V] [Module 𝕜 V]
  [AddCommGroup W] [TopologicalSpace W] [Module 𝕜 W] [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Send a continuous bilinear map to an abstract bilinear map (forgetting continuity). -/
def ContinuousLinearMap.toLinearMap₂ (L : V →L[𝕜] W →L[𝕜] E) : V →ₗ[𝕜] W →ₗ[𝕜] E :=
  (ContinuousLinearMap.coeLM 𝕜).comp L.toLinearMap

end bilinear_maps

lemma hasDerivAt_fourierChar (x : ℝ) :
    HasDerivAt (fun y ↦ fourierChar [y] : ℝ → ℂ)
    (2 * π * I * fourierChar [x]) x := by
  convert hasDerivAt_fourier 1 1 x using 1
  · ext1 y
    rw [fourierChar_apply, fourier_coe_apply]
    congr 1
    push_cast
    ring
  · rw [Int.cast_one, ofReal_one, div_one, mul_one, fourierChar_apply, fourier_coe_apply]
    congr 2
    push_cast
    ring

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier -- special case of VectorFourier theory when e is the standard add char

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v → (w → L(v, w) • f v)`. -/
def mul_L (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) : (W →L[ℝ] E) := (L v).smulRight (f v)

lemma norm_mul_L (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) : ‖mul_L L f v‖ = ‖L v‖ * ‖f v‖ :=
  ContinuousLinearMap.norm_smulRight_apply _ _

/-- The `w`-derivative of the Fourier transform integrand. -/
lemma HasFDerivAt_fourier_transform_integrand_right
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    HasFDerivAt (fun w' : W ↦ fourierChar [-L v w'] • f v)
    ((-2 * ↑π * I) • (fourierChar [-L v w] • mul_L L f v)) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext1 w'
  clear ha
  simp_rw [mul_L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, real_smul, real_smul, smul_eq_mul]
  push_cast
  ring_nf

/-- Norm of the `w`-derivative of the Fourier transform integrand. -/
lemma norm_fderiv_fourier_transform_integrand_right
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    ‖(-2 * ↑π * I) • (fourierChar [-L v w] • mul_L L f v)‖ = (2 * π) * ‖L v‖ * ‖f v‖ :=
  by rw [norm_smul, norm_smul, norm_eq_abs (fourierChar _ : ℂ), abs_coe_circle, one_mul, norm_mul,
    norm_eq_abs I, abs_I, mul_one, norm_mul, norm_eq_abs ((_ : ℝ) : ℂ),
    Complex.abs_of_nonneg pi_pos.le, norm_neg,  norm_eq_abs (2 : ℂ), Complex.abs_two, norm_mul_L,
      ← mul_assoc]

lemma norm_fderiv_fourier_transform_integrand_right_le
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    ‖(-2 * ↑π * I) • (fourierChar [-L v w] • (mul_L L f v))‖
      ≤ (2 * π) * ‖L‖ * ‖v‖ * ‖f v‖ := by
  rw [norm_fderiv_fourier_transform_integrand_right]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  conv_rhs => rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (L.le_op_norm _) two_pi_pos.le

/-- Main theorem of this section: if both `f` and `λ x, ‖x‖ * f x` are integrable, then the
Fourier transform of `f` is has a Frechet derivative (everwhere in its domain) and its derivative is
the Fourier transform of `mul_L L f`. -/
theorem hasFDerivAt_fourier [CompleteSpace E] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)] (L : V →L[ℝ] W →L[ℝ] ℝ)
    {f : V → E} (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (VectorFourier.fourierIntegral fourierChar μ L.toLinearMap₂ f)
      ((-2 * ↑π * I : ℂ) • (VectorFourier.fourierIntegral fourierChar μ L.toLinearMap₂
      (mul_L L f) w)) w := by
  let F : W → V → E := fun w' v ↦ fourierChar [-L v w'] • f v
  let F' : W → V → (W →L[ℝ] E) :=
    fun w' v ↦ (-2 * ↑π * I) • (fourierChar [-L v w'] • mul_L L f v)
  let B : V → ℝ := fun v : V ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 : ∀ (w' : W), Integrable (F w') μ
  · exact fun w' ↦ (VectorFourier.fourier_integral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ L.toLinearMap₂ p.1 p.2)) w').mp hf
  have h1 : ∀ᶠ (w' : W) in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    eventually_of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h2 : Integrable (F w) μ := h0 w
  have h3 : AEStronglyMeasurable (F' w) μ
  · change AEStronglyMeasurable
      ((-2 * ↑π * I : ℂ) • (fun v ↦ (fourierChar [-L v w] • mul_L L f v))) μ
    refine (AEStronglyMeasurable.smul ?_ ?_).const_smul _
    · refine (continuous_subtype_val.comp (continuous_fourierChar.comp ?_)).aestronglyMeasurable
      exact continuous_ofAdd.comp (L.continuous₂.comp (Continuous.Prod.mk_left w)).neg
    · exact aestronglyMeasurable_smulRight L.continuous.aestronglyMeasurable hf.1
  have h4 : (∀ᵐ (v : V) ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v)
  · refine ae_of_all _ (fun v w' _ ↦ ?_)
    exact norm_fderiv_fourier_transform_integrand_right_le L f v w'
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : ∀ᵐ (v : V) ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 →
    HasFDerivAt (fun (w'' : W) ↦ (F w'' v)) (F' w' v) w'
  · refine ae_of_all _ (fun v w' _ ↦ ?_)
    exact HasFDerivAt_fourier_transform_integrand_right L f v w'
  simpa only [integral_smul] using
    hasFDerivAt_integral_of_dominated_of_fderiv_le zero_lt_one h1 h2 h3 h4 h5 h6

end VectorFourier

section inner

variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MeasurableSpace V]
  [BorelSpace V] [FiniteDimensional ℝ V] [CompleteSpace E]

/-- Notation for the Fourier transform on a real inner product space -/
abbrev integralFourier (f : V → E) :=
  VectorFourier.fourierIntegral fourierChar (volume : Measure V) (innerₛₗ ℝ) f

/-- The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
    `fun v ↦ ((-2 * π * I) • f v) ⊗ (innerSL ℝ v)`. -/
theorem InnerProductSpace.hasFDerivAt_fourier {f : V → E} (hf_int : Integrable f)
    (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖)) (x : V) :
    HasFDerivAt (integralFourier f) (integralFourier (fun v ↦
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(2 * π * I) • f v)) ∘L (innerSL ℝ) v)) x) x := by
  convert VectorFourier.hasFDerivAt_fourier (innerSL ℝ) hf_int hvf_int x
  simp_rw [integralFourier, VectorFourier.fourierIntegral, ← integral_smul (-2 * ↑π * I : ℂ)]
  congr 1 with v w
  let p : ℂ := ↑(fourierChar (Multiplicative.ofAdd (-((innerₛₗ ℝ) v) x)))
  change (p • (ContinuousLinearMap.toSpanSingleton ℝ (-(2 * ↑π * I) • f v)).comp
    (innerSL ℝ v)) w = ((-2 * ↑π * I) • p • VectorFourier.mul_L (innerSL ℝ) f v) w
  rw [smul_comm _ p, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply]
  congr 1
  rw [ContinuousLinearMap.toSpanSingleton_apply, smul_comm, ContinuousLinearMap.smul_apply,
    neg_mul, neg_mul]
  rfl

end inner

section scalar

open VectorFourier

lemma hasDerivAt_fourierIntegral [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) (w : ℝ) :
    HasDerivAt (𝓕 f) ((-2 * ↑π * I : ℂ) • 𝓕 (fun x : ℝ ↦ x • f x) w) w := by
  have hf'' : Integrable (fun v : ℝ ↦ ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using hf'.norm
  let L := ContinuousLinearMap.mul ℝ ℝ
  have h_int : Integrable fun v ↦ mul_L L f v
  · convert ((ContinuousLinearMap.ring_lmap_equiv_self ℝ
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' with v
    ext1
    rw [mul_L, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', mul_one,
      ContinuousLinearMap.map_smul]
    exact congr_arg (fun x ↦ v • x) (one_smul ℝ (f v)).symm
  rw [fourier_integral_convergent_iff continuous_fourierChar L.continuous₂ w] at h_int
  convert (hasFDerivAt_fourier L hf hf'' w).hasDerivAt
  simp_rw [Real.fourierIntegral, Fourier.fourierIntegral, VectorFourier.fourierIntegral,
    ContinuousLinearMap.smul_apply]
  erw [ContinuousLinearMap.integral_apply h_int]
  simp_rw [ContinuousLinearMap.smul_apply, mul_L, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.mul_apply', mul_one]

end scalar

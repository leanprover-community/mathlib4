/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, David Loeffler, Heather Macbeth
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

lemma Real.hasDerivAt_fourierChar (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ (fourierChar (Multiplicative.ofAdd y) : ℂ))
      (2 * π * I * (fourierChar (Multiplicative.ofAdd x) : ℂ)) x := by
  have h1 (y : ℝ) : (fourierChar (Multiplicative.ofAdd y) : ℂ) =
    fourier 1 (y : UnitAddCircle)
  · rw [fourierChar_apply, fourier_coe_apply]
    push_cast
    ring_nf
  simpa only [h1, Int.cast_one, ofReal_one, div_one, mul_one]
    using hasDerivAt_fourier 1 1 x

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

namespace VectorFourier

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E)

/-- Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v → (w → -2 * π * I * L(v, w) • f v)`. -/
def mul_L (v : V) : (W →L[ℝ] E) := -(2 * π * I) • (L v).smulRight (f v)

/-- Alternate description of `VectorFourier.mulL`. -/
lemma mulL_eq_toSpanSingleton_comp : mul_L L f =
    fun v ↦ ((ContinuousLinearMap.toSpanSingleton ℝ (-(2 * π * I) • f v)) ∘L L v) := by
  ext v v'
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_comm,
    VectorFourier.mul_L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]

/-- The `w`-derivative of the Fourier transform integrand. -/
lemma hasFDerivAt_fourier_transform_integrand_right (v : V) (w : W) :
    HasFDerivAt (fun w' ↦ fourierChar [-L v w'] • f v) (fourierChar [-L v w] • mul_L L f v) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext1 w'
  simp_rw [mul_L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, real_smul, real_smul, smul_eq_mul]
  push_cast
  ring_nf

/-- Norm of the `w`-derivative of the Fourier transform integrand. -/
lemma norm_fderiv_fourier_transform_integrand_right
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    ‖fourierChar [-L v w] • mul_L L f v‖ = (2 * π) * ‖L v‖ * ‖f v‖ :=
  by rw [norm_smul, norm_eq_abs (fourierChar _ : ℂ), abs_coe_circle, one_mul, mul_L, norm_smul,
    norm_neg, norm_mul, norm_mul, norm_eq_abs I, abs_I, mul_one, norm_eq_abs ((_ : ℝ) : ℂ),
    Complex.abs_of_nonneg pi_pos.le, norm_eq_abs (2 : ℂ), Complex.abs_two,
    ContinuousLinearMap.norm_smulRight_apply, ← mul_assoc]

lemma norm_fderiv_fourier_transform_integrand_right_le (v : V) (w : W) :
    ‖fourierChar [-L v w] • (mul_L L f v)‖ ≤ (2 * π) * ‖L‖ * ‖v‖ * ‖f v‖ := by
  rw [norm_fderiv_fourier_transform_integrand_right]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  conv_rhs => rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (L.le_op_norm _) two_pi_pos.le

variable {f}

/-- Main theorem of this section: if both `f` and `x ↦ ‖x‖ * ‖f x‖` are integrable, then the
Fourier transform of `f` has a Fréchet derivative (everywhere in its domain) and its derivative is
the Fourier transform of `mul_L L f`. -/
theorem hasFDerivAt_fourier [CompleteSpace E] [MeasurableSpace V] [BorelSpace V] {μ : Measure V}
    [SecondCountableTopologyEither V (W →L[ℝ] ℝ)]
    (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt (VectorFourier.fourierIntegral fourierChar μ L.toLinearMap₂ f)
      (VectorFourier.fourierIntegral fourierChar μ L.toLinearMap₂ (mul_L L f) w) w := by
  let F : W → V → E := fun w' v ↦ fourierChar [-L v w'] • f v
  let F' : W → V → W →L[ℝ] E := fun w' v ↦ fourierChar [-L v w'] • mul_L L f v
  let B : V → ℝ := fun v ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 (w' : W) : Integrable (F w') μ :=
    (VectorFourier.fourier_integral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ L.toLinearMap₂ p.1 p.2)) w').mp hf
  have h1 : ∀ᶠ w' in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    eventually_of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h2 : Integrable (F w) μ := h0 w
  have h3 : AEStronglyMeasurable (F' w) μ
  · change AEStronglyMeasurable (fun v ↦ fourierChar [-L v w] • mul_L L f v) μ
    refine AEStronglyMeasurable.smul ?_ ?_
    · refine (continuous_subtype_val.comp (continuous_fourierChar.comp ?_)).aestronglyMeasurable
      exact continuous_ofAdd.comp (L.continuous₂.comp (Continuous.Prod.mk_left w)).neg
    · apply AEStronglyMeasurable.const_smul'
      have aux0 : Continuous fun p : (W →L[ℝ] ℝ) × E ↦ p.1.smulRight p.2 :=
        (ContinuousLinearMap.smulRightL ℝ W E).continuous₂
      have aux1 : AEStronglyMeasurable (fun v ↦ (L v, f v)) μ :=
        L.continuous.aestronglyMeasurable.prod_mk hf.1
      apply aux0.comp_aestronglyMeasurable aux1
  have h4 : (∀ᵐ v ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v)
  · refine ae_of_all _ (fun v w' _ ↦ ?_)
    exact norm_fderiv_fourier_transform_integrand_right_le L f v w'
  have h5 : Integrable B μ := by simpa only [← mul_assoc] using hf'.const_mul (2 * π * ‖L‖)
  have h6 : ∀ᵐ v ∂μ, ∀ w', w' ∈ Metric.ball w 1 → HasFDerivAt (fun x ↦ F x v) (F' w' v) w' :=
    ae_of_all _ (fun v w' _ ↦ hasFDerivAt_fourier_transform_integrand_right L f v w')
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le one_pos h1 h2 h3 h4 h5 h6

section inner

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [SecondCountableTopology V]
  [MeasurableSpace V] [BorelSpace V] [CompleteSpace E]

/-- Notation for the Fourier transform on a real inner product space -/
abbrev integralFourier (f : V → E) (μ : Measure V := by volume_tac) :=
  fourierIntegral fourierChar μ (innerₛₗ ℝ) f

/-- The Fréchet derivative of the Fourier transform of `f` is the Fourier transform of
    `fun v ↦ ((-2 * π * I) • f v) ⊗ (innerSL ℝ v)`. -/
theorem InnerProductSpace.hasFDerivAt_fourier {f : V → E} {μ : Measure V}
    (hf_int : Integrable f μ) (hvf_int : Integrable (fun v ↦ ‖v‖ * ‖f v‖) μ) (x : V) :
    HasFDerivAt (integralFourier f μ) (integralFourier (fun v ↦
      ((ContinuousLinearMap.toSpanSingleton ℝ (-(2 * π * I) • f v)) ∘L (innerSL ℝ) v)) μ x) x := by
  haveI : SecondCountableTopologyEither V (V →L[ℝ] ℝ) :=
    secondCountableTopologyEither_of_left V _ -- for some reason it fails to synthesize this?
  simpa only [VectorFourier.mulL_eq_toSpanSingleton_comp]
    using VectorFourier.hasFDerivAt_fourier (innerSL ℝ) hf_int hvf_int x

end inner

end VectorFourier

open VectorFourier

lemma hasDerivAt_fourierIntegral [CompleteSpace E]
    {f : ℝ → E} (hf : Integrable f) (hf' : Integrable (fun x : ℝ ↦ x • f x)) (w : ℝ) :
    HasDerivAt (𝓕 f) (𝓕 (fun x : ℝ ↦ (-2 * ↑π * I * x) • f x) w) w := by
  have hf'' : Integrable (fun v : ℝ ↦ ‖v‖ * ‖f v‖) := by simpa only [norm_smul] using hf'.norm
  let L := ContinuousLinearMap.mul ℝ ℝ
  have h_int : Integrable fun v ↦ mul_L L f v
  · suffices : Integrable fun v ↦ ContinuousLinearMap.smulRight (L v) (f v)
    · simpa only [mul_L, neg_smul, neg_mul, Pi.smul_apply] using this.smul (-2 * π * I)
    convert ((ContinuousLinearMap.ring_lmap_equiv_self ℝ
      E).symm.toContinuousLinearEquiv.toContinuousLinearMap).integrable_comp hf' using 2 with v
    apply ContinuousLinearMap.ext_ring
    rw [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', mul_one,
      ContinuousLinearMap.map_smul]
    exact congr_arg (fun x ↦ v • x) (one_smul ℝ (f v)).symm
  rw [fourier_integral_convergent_iff continuous_fourierChar L.continuous₂ w] at h_int
  convert (hasFDerivAt_fourier L hf hf'' w).hasDerivAt using 1
  erw [ContinuousLinearMap.integral_apply h_int]
  simp_rw [ContinuousLinearMap.smul_apply, mul_L, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.mul_apply', mul_one,
    ← neg_mul, mul_smul]
  rfl

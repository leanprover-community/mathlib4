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
-/

noncomputable section

open Real MeasureTheory Filter TopologicalSpace

open scoped FourierTransform Topology

section SmulRight

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- `ContinuousLinearMap.smulRight` as a linear map (in the second variable only). -/
noncomputable def smulRight_lm
    {A : Type*} [NormedAddCommGroup A] [NormedSpace 𝕜 A] (t : A →L[𝕜] 𝕜)
    (B : Type*) [NormedAddCommGroup B] [NormedSpace 𝕜 B] :
    B →ₗ[𝕜] (A →L[𝕜] B) where
  toFun := t.smulRight
  map_add' := by
    intros b b'
    ext1 a
    simp only [ContinuousLinearMap.smulRight_apply, smul_add, ContinuousLinearMap.add_apply]
  map_smul' := by
    intros x b
    ext1 a
    simp only [ContinuousLinearMap.smulRight_apply, RingHom.id_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply]
    rw [smul_comm]

variable (𝕜)

/-- `ContinuousLinearMap.smulRight` as a bilinear map. -/
noncomputable def smulRight_lm₂
    (A B : Type*) [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] :
    (A →L[𝕜] 𝕜) →ₗ[𝕜] (B →ₗ[𝕜] (A →L[𝕜] B)) where
  toFun := fun t ↦ smulRight_lm t B
  map_add' := fun t u ↦ by
    ext
    simp only [smulRight_lm, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.add_apply, add_smul, LinearMap.add_apply]
  map_smul' := fun r t ↦ by
    ext
    simp only [smulRight_lm, LinearMap.coe_mk, AddHom.coe_mk, ContinuousLinearMap.smulRight_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply, smul_eq_mul, mul_smul, RingHom.id_apply,
      LinearMap.smul_apply]

/-- `ContinuousLinearMap.smulRight` as a continuous bilinear map. --/
noncomputable def smulRight_clm₂ (A B : Type*) [NormedAddCommGroup A] [NormedSpace 𝕜 A]
    [NormedAddCommGroup B] [NormedSpace 𝕜 B] :
    (A →L[𝕜] 𝕜) →L[𝕜] (B →L[𝕜] (A →L[𝕜] B)) :=
  LinearMap.mkContinuous₂ (smulRight_lm₂ 𝕜 A B) 1 (by simpa only [one_mul] using
    (fun t b ↦ le_of_eq (ContinuousLinearMap.norm_smulRight_apply t b)))

lemma aestronglyMeasurable_smulRight {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A] [SecondCountableTopology (A →L[ℝ] ℝ)]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [SecondCountableTopology B] [MeasurableSpace B]
    [BorelSpace B] {f : X → A →L[ℝ] ℝ} {g : X → B}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ) :
    AEStronglyMeasurable (fun x : X ↦ (f x).smulRight (g x)) μ := by
  haveI : SecondCountableTopologyEither ((A →L[ℝ] ℝ) × B) (A →L[ℝ] B) :=
    secondCountableTopologyEither_of_left _ _
  exact (smulRight_clm₂ ℝ A B).continuous₂.aestronglyMeasurable.comp_aemeasurable
    (hf.prod_mk hg).aemeasurable

end SmulRight

variable {E V W : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

lemma hasDerivAt_fourierChar (x : ℝ) :
    HasDerivAt (fun y ↦ Real.fourierChar [y] : ℝ → ℂ)
    (2 * π * Complex.I * Real.fourierChar [x]) x := by
  convert hasDerivAt_fourier 1 1 x using 1
  · ext1 y
    rw [fourierChar_apply, fourier_coe_apply]
    congr 1
    push_cast
    ring
  · rw [Int.cast_one, Complex.ofReal_one, div_one, mul_one, fourierChar_apply, fourier_coe_apply]
    congr 2
    push_cast
    ring

section bilinear_maps

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Send a continuous bilinear map to an abstract bilinear map (forgetting continuity). -/
def to_bilinear_map (L : V →L[ℝ] W →L[ℝ] ℝ) : V →ₗ[ℝ] W →ₗ[ℝ] ℝ :=
  (ContinuousLinearMap.coeLM ℝ).comp L.toLinearMap

lemma continuous_to_bilinear_map (L : V →L[ℝ] W →L[ℝ] ℝ) :
    Continuous (fun p : V × W ↦ L p.1 p.2) := L.continuous₂

end bilinear_maps

namespace VectorFourier -- special case of VectorFourier theory when e is the standard add char

variable [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- Send a function `f : V → E` to the function `f : V → Hom (W, E)` given by
`v → (w → L(v, w) • f v)`. -/
def mul_L (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) : (W →L[ℝ] E) := (L v).smulRight (f v)

lemma norm_mul_L
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) :
    ‖mul_L L f v‖ = ‖L v‖ * ‖f v‖ :=
  ContinuousLinearMap.norm_smulRight_apply _ _

/-- The `w`-derivative of the Fourier transform integrand. -/
lemma HasFDerivAt_fourier_transform_integrand_right
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    HasFDerivAt (fun w' : W ↦ fourierChar [-L v w'] • f v)
    ((-2 * ↑π * Complex.I) • (fourierChar [-L v w] • mul_L L f v)) w := by
  have ha : HasFDerivAt (fun w' : W ↦ L v w') (L v) w := ContinuousLinearMap.hasFDerivAt (L v)
  convert ((hasDerivAt_fourierChar (-L v w)).hasFDerivAt.comp w ha.neg).smul_const (f v)
  ext1 w'
  clear ha
  simp_rw [mul_L, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, ← smul_assoc, smul_comm,
    ← smul_assoc, Complex.real_smul, Complex.real_smul, smul_eq_mul]
  push_cast
  ring_nf

/-- Norm of the `w`-derivative of the Fourier transform integrand. -/
lemma norm_fderiv_fourier_transform_integrand_right
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    ‖(-2 * ↑π * Complex.I) • (fourierChar [-L v w] • mul_L L f v)‖ = (2 * π) * ‖L v‖ * ‖f v‖ :=
  by rw [norm_smul, norm_smul, Complex.norm_eq_abs (↑(fourierChar _)), abs_coe_circle,
      one_mul, norm_mul, Complex.norm_eq_abs Complex.I, Complex.abs_I, mul_one,
      norm_mul, Complex.norm_eq_abs (↑(_: ℝ)), Complex.abs_of_nonneg pi_pos.le, norm_neg,
      Complex.norm_eq_abs 2, Complex.abs_two, norm_mul_L, ← mul_assoc]

lemma norm_fderiv_fourier_transform_integrand_right_le
    (L : V →L[ℝ] W →L[ℝ] ℝ) (f : V → E) (v : V) (w : W) :
    ‖(-2 * ↑π * Complex.I) • (fourierChar [-L v w] • (mul_L L f v))‖
      ≤ (2 * π) * ‖L‖ * ‖v‖ * ‖f v‖ := by
  rw [norm_fderiv_fourier_transform_integrand_right]
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  conv_rhs => rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (L.le_op_norm _) two_pi_pos.le

/-- Main theorem of this section: if both `f` and `λ x, ‖x‖ * f x` are integrable, then the
Fourier transform of `f` is has a Frechet derivative (everwhere in its domain) and its derivative is
the Fourier transform of `mul_L L f`. -/
theorem hasFDerivAt_fourier [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [SecondCountableTopology (W →L[ℝ] ℝ)]
    (L : V →L[ℝ] W →L[ℝ] ℝ)
    {f : V → E} (hf : Integrable f μ) (hf' : Integrable (fun v : V ↦ ‖v‖ * ‖f v‖) μ) (w : W) :
    HasFDerivAt
      (VectorFourier.fourierIntegral fourierChar μ (to_bilinear_map L) f)
      ((-2 * ↑π * Complex.I : ℂ) • (VectorFourier.fourierIntegral fourierChar μ (to_bilinear_map L)
      (mul_L L f) w)) w := by
  let F : W → V → E := fun w' v ↦ fourierChar [-L v w'] • f v
  let F' : W → V → (W →L[ℝ] E) :=
    fun w' v ↦ (-2 * ↑π * Complex.I) • (fourierChar [-L v w'] • mul_L L f v)
  let B : V → ℝ := fun v : V ↦ 2 * π * ‖L‖ * ‖v‖ * ‖f v‖
  have h0 : ∀ (w' : W), Integrable (F w') μ
  · exact fun w' ↦ (VectorFourier.fourier_integral_convergent_iff continuous_fourierChar
      (by apply L.continuous₂ : Continuous (fun p : V × W ↦ (to_bilinear_map L) p.1 p.2)) w').mp hf
  have h1 : ∀ᶠ (w' : W) in 𝓝 w, AEStronglyMeasurable (F w') μ :=
    eventually_of_forall (fun w' ↦ (h0 w').aestronglyMeasurable)
  have h2 : Integrable (F w) μ := h0 w
  have h3 : AEStronglyMeasurable (F' w) μ
  · change AEStronglyMeasurable
      ((-2 * ↑π * Complex.I : ℂ) • (fun v ↦ (fourierChar [-L v w] • mul_L L f v))) μ
    apply AEStronglyMeasurable.const_smul
    apply AEStronglyMeasurable.smul
    · refine (continuous_subtype_val.comp (continuous_fourierChar.comp ?_)).aestronglyMeasurable
      exact continuous_ofAdd.comp (L.continuous₂.comp (Continuous.Prod.mk_left w)).neg
    · borelize E
      simp_rw [mul_L]
      apply aestronglyMeasurable_smulRight
      · apply Continuous.aestronglyMeasurable
        exact L.continuous
      · exact hf.1
  have h4 : (∀ᵐ (v : V) ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 → ‖F' w' v‖ ≤ B v)
  · refine ae_of_all _ (fun v w' _ ↦ ?_)
    exact norm_fderiv_fourier_transform_integrand_right_le L f v w'
  have h5 : Integrable B μ
  · convert hf'.const_mul (2 * π * ‖L‖) using 1
    ext1 v
    dsimp only [B]
    ring
  have h6 : ∀ᵐ (v : V) ∂μ, ∀ (w' : W), w' ∈ Metric.ball w 1 →
    HasFDerivAt (fun (w'' : W) ↦ (F w'' v)) (F' w' v) w'
  · refine ae_of_all _ (fun v w' _ ↦ ?_)
    exact HasFDerivAt_fourier_transform_integrand_right L f v w'
  simpa only [integral_smul]
    using hasFDerivAt_integral_of_dominated_of_fderiv_le zero_lt_one h1 h2 h3 h4 h5 h6

end VectorFourier

section scalar

/- This stuff is leading up to a not-yet-ported lemma which reformulates the result as
`HasDerivAt` rather than `HasFDerivAt` when `V = ℝ`. The preliminaries below all compile OK but
I didn't manage to port the main result yet, since the mathlib3 lemma
"continuous_linear_map.to_linear_map_eq_coe" doesn't seem to have a direct analogue in mathlib4.-/

namespace ContinuousLinearMap

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly equivalent
to `M`. (See `ring_lmap_equiv_self` for a stronger statement.) -/
def ring_lmap_equiv_selfₗ (𝕜 M : Type*)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M] :
    (𝕜 →L[𝕜] M) ≃ₗ[𝕜] M where
  toFun := fun f ↦ f 1
  invFun := (ContinuousLinearMap.id 𝕜 𝕜).smulRight
  map_smul' := fun a f ↦ by simp only [coe_smul', Pi.smul_apply, RingHom.id_apply]
  map_add' := fun f g ↦ by simp only [add_apply]
  left_inv := fun f ↦ by ext; simp only [smulRight_apply, coe_id', id.def, one_smul]
  right_inv := fun m ↦ by simp only [smulRight_apply, id_apply, one_smul]

/-- If `M` is a normed space over `𝕜`, then the space of maps `𝕜 →L[𝕜] M` is linearly isometrically
equivalent to `M`. -/
def ring_lmap_equiv_self (𝕜 M : Type*)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M] :
    (𝕜 →L[𝕜] M) ≃ₗᵢ[𝕜] M where
  toLinearEquiv := ContinuousLinearMap.ring_lmap_equiv_selfₗ 𝕜 M
  norm_map' := fun f ↦ by
    dsimp only [ContinuousLinearMap.ring_lmap_equiv_selfₗ]
    rw [LinearEquiv.coe_mk]
    apply eq_of_le_of_not_lt
    · simpa only [norm_one, mul_one] using ContinuousLinearMap.le_op_norm f 1
    · push_neg
      refine ContinuousLinearMap.op_norm_le_bound' f (norm_nonneg _) (fun x _ ↦ ?_)
      rw [(by rw [smul_eq_mul, mul_one] : f x = f (x • 1)), ContinuousLinearMap.map_smul,
        norm_smul, mul_comm]

lemma ring_lmap_equiv_self_apply (𝕜 : Type*) {M : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] (f : 𝕜 →L[𝕜] M) :
    (ring_lmap_equiv_self 𝕜 M) f = f 1 :=
  rfl

lemma ring_lmap_equiv_self_symm_apply (𝕜 : Type*) {M : Type*} (m : M)
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup M] [NormedSpace 𝕜 M] :
    (ring_lmap_equiv_self 𝕜 M).symm m = (ContinuousLinearMap.id 𝕜 𝕜).smulRight m :=
  rfl

end ContinuousLinearMap

/-- the lemma which doesn't work


lemma has_deriv_at_fourier_integral [complete_space E] [second_countable_topology E]
  {f : ℝ → E} (hf : integrable f) (hf' : integrable (λ x : ℝ, x • f x)) (w : ℝ) :
  has_deriv_at (fourier_integral f)
    ((-2 * ↑π * complex.I : ℂ) • fourier_integral (λ x : ℝ, x • f x) w) w :=
begin
  have hf'' : integrable (λ v : ℝ, ‖v‖ * ‖f v‖), by simpa only [norm_smul] using hf'.norm,
  have := (vector_fourier.has_fderiv_at_fourier
    (continuous_linear_map.mul ℝ ℝ) hf hf'' w).has_deriv_at,
  convert this,
  rw [real.fourier_integral, vector_fourier.fourier_integral],
  have : (∫ (v : ℝ), real.fourier_char [-(to_bilinear_map (continuous_linear_map.mul ℝ ℝ)) v w] •
    vector_fourier.mul_L (continuous_linear_map.mul ℝ ℝ) f v).to_linear_map 1 =
    (∫ (v : ℝ), real.fourier_char [-(to_bilinear_map (continuous_linear_map.mul ℝ ℝ)) v w] •
      ((vector_fourier.mul_L (continuous_linear_map.mul ℝ ℝ) f v) 1)),
  { change (∫ (v : ℝ), real.fourier_char[-(to_bilinear_map (continuous_linear_map.mul ℝ ℝ)) v w] •
      vector_fourier.mul_L (continuous_linear_map.mul ℝ ℝ) f v).to_linear_map 1
      with (∫ (v : ℝ), real.fourier_char[-(to_bilinear_map (continuous_linear_map.mul ℝ ℝ)) v w] •
      vector_fourier.mul_L (continuous_linear_map.mul ℝ ℝ) f v) 1,
    rw continuous_linear_map.integral_apply,
    { refl },
    { refine vector_fourier.fourier_integral_convergent continuous_fourier_char _ _ _,
      { exact (continuous_linear_map.mul ℝ ℝ).continuous₂ },
      { let A : (ℝ →L[ℝ] E) ≃ₗᵢ[ℝ] E := continuous_linear_map.ring_lmap_equiv_self ℝ E,
        have := continuous_linear_map.integrable_comp
          A.symm.to_continuous_linear_equiv.to_continuous_linear_map hf',
        convert this,
        ext1 x,
        apply continuous_linear_map.ext_ring,
        rw [vector_fourier.mul_L, continuous_linear_equiv.to_continuous_linear_map,
          continuous_linear_map.coe_mk', linear_map.coe_mk, linear_map.to_fun_eq_coe,
          linear_equiv.coe_to_linear_map, continuous_linear_equiv.coe_to_linear_equiv,
          linear_isometry_equiv.coe_to_continuous_linear_equiv,
          continuous_linear_map.ring_lmap_equiv_self_symm_apply,
          continuous_linear_map.smul_right_apply, continuous_linear_map.smul_right_apply,
          continuous_linear_map.id_apply, continuous_linear_map.mul_apply', mul_one, one_smul] }}},
  rw [←continuous_linear_map.to_linear_map_eq_coe, this],
  congr' 1 with x : 1,
  simp_rw vector_fourier.mul_L,
  rw [continuous_linear_map.smul_right_apply, continuous_linear_map.mul_apply', mul_one],
end



-/
end scalar

/-
Copyright (c) 2025 Jack Valmadre. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Valmadre
-/
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Function.L2Space

/-!
# TODO: Move into FourierTransform.lean
-/

open MeasureTheory
open scoped ENNReal FourierTransform InnerProductSpace

variable {𝕜 V E F : Type*} [RCLike 𝕜] [NormedAddCommGroup V]
  [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

section Basic

theorem Real.conj_fourierChar (x : ℝ) : starRingEnd ℂ (𝐞 x) = 𝐞 (-x) := by
  simp only [fourierChar, AddChar.coe_mk, mul_neg, Circle.exp_neg]
  exact .symm <| Circle.coe_inv_eq_conj _

@[simp]
theorem Real.fourierIntegral_zero : 𝓕 (0 : V → E) = 0 := by
  ext ξ
  simp [fourierIntegral_eq]

theorem Real.fourierIntegral_add {f g : V → E} (hf : Integrable f volume)
    (hg : Integrable g volume) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add continuous_fourierChar continuous_inner hf hg

-- TODO: Is `r : 𝕜` more general than needed? `VectorFourier` uses `r : ℂ`.
theorem Real.fourierIntegral_const_smul
    {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
    (r : 𝕜) (f : V → E) : 𝓕 (r • f) = r • 𝓕 f := by
  ext ξ
  simpa [fourierIntegral_eq, smul_comm (𝐞 _)] using integral_smul r _

theorem Real.fourierIntegral_continuous {f : V → E} (hf : Integrable f (volume : Measure V)) :
    Continuous (𝓕 f) :=
  VectorFourier.fourierIntegral_continuous continuous_fourierChar continuous_inner hf

-- TODO: Provide for `VectorFourier.fourierIntegral`?
theorem Real.fourierIntegral_congr_ae {f g : V → E} (h : f =ᵐ[volume] g) : 𝓕 f = 𝓕 g := by
  ext ξ
  refine integral_congr_ae ?_
  filter_upwards [h] with x h
  rw [h]

theorem Real.fourierIntegralInv_congr_ae {f g : V → E} (h : f =ᵐ[volume] g) : 𝓕⁻ f = 𝓕⁻ g := by
  ext ξ
  refine integral_congr_ae ?_
  filter_upwards [h] with x h
  rw [h]

end Basic

section InnerProduct

-- TODO: Move into `Mathlib/Analysis/Fourier/FourierTransform.lean`?
-- TODO: Check type classes for `V`.
-- TODO: Generalize to bilinear `L`?

-- This cannot be generalized from `⟪·, ·⟫_ℂ` to `⟪·, ·⟫_𝕜` with e.g. `NormedField 𝕜`.
-- Firstly, we need `RCLike 𝕜` for e.g. `InnerProductSpace 𝕜 F`.
-- Then, we cannot use `𝕜 = ℝ` because we need e.g. `Algebra ℂ 𝕜` and `IsScalarTower ℂ 𝕜 F` for
-- `⟪f w, 𝐞 (-⟪v, w⟫_ℝ) • g v⟫ = 𝐞 (-⟪v, w⟫_ℝ) • ⟪f w, g v⟫ = ⟪𝐞 ⟪w, v⟫_ℝ • f w, g v⟫`.
-- Therefore, we may as well restrict ourselves to `𝕜 = ℂ`.

/-- The L^2 inner product of a function with the Fourier transform of another is equal to the
L^2 inner product of its inverse Fourier transform with the other function.

This is useful for proving Plancherel's theorem.
Note that, unlike Plancherel's theorem, it does not require `Continuous`. -/
theorem Real.integral_inner_fourier_eq_integral_fourierInv_inner
    {f g : V → F} (hf_int : Integrable f) (hg_int : Integrable g) :
    ∫ w, ⟪f w, 𝓕 g w⟫_ℂ = ∫ w, ⟪𝓕⁻ f w, g w⟫_ℂ := by
  calc ∫ w, ⟪f w, 𝓕 g w⟫_ℂ
  _ = ∫ w, ∫ v, 𝐞 (-⟪w, v⟫_ℝ) • ⟪f w, g v⟫_ℂ := by
    simp only [fourierIntegral_eq]
    refine congrArg (integral _) (funext fun w ↦ ?_)
    calc ⟪f w, ∫ v, 𝐞 (-⟪v, w⟫_ℝ) • g v⟫_ℂ
    _ = ∫ v, ⟪f w, 𝐞 (-⟪v, w⟫_ℝ) • g v⟫_ℂ := by
      refine (integral_inner ?_ _).symm
      exact (fourierIntegral_convergent_iff w).mpr hg_int
    _ = ∫ v, 𝐞 (-⟪v, w⟫_ℝ) • ⟪f w, g v⟫_ℂ := by
      refine congrArg (integral _) (funext fun v ↦ ?_)
      simp only [Circle.smul_def]  -- TODO: Need `InnerProductSpace ℂ` for this?
      exact inner_smul_right _ _ _
    _ = ∫ v, 𝐞 (-⟪w, v⟫_ℝ) • ⟪f w, g v⟫_ℂ := by simp only [real_inner_comm w]
  -- Change order of integration.
  _ = ∫ v, ∫ w, 𝐞 (-⟪w, v⟫_ℝ) • ⟪f w, g v⟫_ℂ := by
    refine integral_integral_swap ?_
    simp only [Function.uncurry_def]
    -- TODO: Clean up. `h_prod` below could come from `this`?
    suffices Integrable (fun p : V × V ↦ ⟪f p.1, g p.2⟫_ℂ) (volume.prod volume) by
      refine (integrable_norm_iff (.smul ?_ this.1)).mp ?_
      · exact (continuous_fourierChar.comp continuous_inner.neg).aestronglyMeasurable
      simp only [Circle.norm_smul]
      exact (integrable_norm_iff this.1).mpr this
    have h_prod : AEStronglyMeasurable (fun p : V × V ↦ ⟪f p.1, g p.2⟫_ℂ) (volume.prod volume) :=
      hf_int.1.fst.inner hg_int.1.snd
    refine (integrable_prod_iff h_prod).mpr ⟨?_, ?_⟩
    · simp only  -- TODO: Some way to avoid this?
      exact .of_forall fun _ ↦ .const_inner _ hg_int
    · simp only
      refine .mono' (g := fun w ↦ ∫ v, ‖f w‖ * ‖g v‖) ?_ ?_ (.of_forall fun w ↦ ?_)
      · simp_rw [integral_mul_left]
        exact hf_int.norm.mul_const _
      · exact (h_prod).norm.integral_prod_right'
      refine norm_integral_le_of_norm_le (hg_int.norm.const_mul _) (.of_forall fun v ↦ ?_)
      rw [norm_norm]
      exact norm_inner_le_norm _ _
  _ = ∫ w, ⟪𝓕⁻ f w, g w⟫_ℂ := by
    refine congrArg (integral _) (funext fun v ↦ ?_)
    -- TODO: Are the nested calcs confusing?
    calc ∫ w, 𝐞 (-⟪w, v⟫_ℝ) • ⟪f w, g v⟫_ℂ
    -- Take conjugate to move `f w` to the right of the inner product.
    _ = ∫ w, starRingEnd ℂ (𝐞 ⟪w, v⟫_ℝ • ⟪g v, f w⟫_ℂ) := by
      simp [Circle.smul_def, conj_fourierChar]
    _ = starRingEnd ℂ ⟪g v, ∫ w, 𝐞 ⟪w, v⟫_ℝ • f w⟫_ℂ := by
      simp only [integral_conj]
      refine congrArg (starRingEnd ℂ) ?_
      calc ∫ w, 𝐞 ⟪w, v⟫_ℝ • ⟪g v, f w⟫_ℂ
      _ = ∫ w, ⟪g v, 𝐞 ⟪w, v⟫_ℝ • f w⟫_ℂ := by simp [Circle.smul_def, inner_smul_right]
      _ = ⟪g v, ∫ w, 𝐞 ⟪w, v⟫_ℝ • f w⟫_ℂ := by
        refine integral_inner ?_ _
        suffices Integrable (fun w ↦ 𝐞 (-⟪w, -v⟫_ℝ) • f w) volume by simpa using this
        exact (fourierIntegral_convergent_iff (-v)).mpr hf_int
    _ = ⟪∫ w, 𝐞 ⟪w, v⟫_ℝ • f w, g v⟫_ℂ := by simp_rw [inner_conj_symm]
    _ = ⟪𝓕⁻ f v, g v⟫_ℂ := by simp_rw [fourierIntegralInv_eq]

-- TODO: Provide variant for `Continuous g`?
/-- The Fourier transform preserves the L^2 inner product. -/
theorem Real.integral_inner_fourier_eq_integral_inner {f g : V → F} (hf_cont : Continuous f)
    (hf_int : Integrable f) (hf_int_fourier : Integrable (𝓕 f)) (hg_int : Integrable g) :
    ∫ ξ, ⟪𝓕 f ξ, 𝓕 g ξ⟫_ℂ = ∫ x, ⟪f x, g x⟫_ℂ := by
  have := integral_inner_fourier_eq_integral_fourierInv_inner
    hf_int_fourier hg_int
  simp only [Continuous.fourier_inversion hf_cont hf_int hf_int_fourier] at this
  exact this

/-- Plancherel's theorem: The Fourier transform preserves the L^2 norm.

Requires that the norm of `F` is defined by an inner product. -/
theorem Real.integral_norm_sq_fourier_eq_integral_norm_sq {f : V → F} (hf_cont : Continuous f)
    (hf_int : Integrable f) (hf_int_fourier : Integrable (𝓕 f)) :
    ∫ ξ, ‖𝓕 f ξ‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have := integral_inner_fourier_eq_integral_inner hf_cont hf_int hf_int_fourier hf_int
  simp only [inner_self_eq_norm_sq_to_K] at this
  simp only [← RCLike.ofReal_pow] at this
  simp only [integral_ofReal] at this
  simpa using this

-- TODO: Are the assumptions general enough to be useful?
-- TODO: Is it necessary to assume `Memℒp (𝓕 f) 2 volume`?
/-- Plancherel's theorem for continuous functions in L^1 ∩ L^2. -/
theorem Real.eLpNorm_fourier_two_eq_eLpNorm_two {f : V → F} (hf_cont : Continuous f)
    (hf_int : Integrable f) (hf_int2 : Memℒp f 2 volume) (hf_int_fourier : Integrable (𝓕 f))
    (hf_int2_fourier : Memℒp (𝓕 f) 2 volume) :
    eLpNorm (𝓕 f) 2 volume = eLpNorm f 2 volume := by
  rw [Memℒp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top hf_int2]
  rw [Memℒp.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.two_ne_top hf_int2_fourier]
  congr 2
  simpa using integral_norm_sq_fourier_eq_integral_norm_sq hf_cont hf_int hf_int_fourier

end InnerProduct

section Scalar

-- TODO: Adjust typeclasses?
theorem Real.conj_fourierIntegral (f : V → ℂ) (ξ : V) :
    starRingEnd ℂ (𝓕 f ξ) = 𝓕 (fun x ↦ starRingEnd ℂ (f x)) (-ξ) := by
  simp only [fourierIntegral_eq]
  refine Eq.trans integral_conj.symm ?_
  simp [Circle.smul_def, conj_fourierChar]

theorem Real.fourierIntegral_conj (f : V → ℂ) (ξ : V) :
    𝓕 (fun x ↦ starRingEnd ℂ (f x)) ξ = starRingEnd ℂ (𝓕 f (-ξ)) := by
  simp only [fourierIntegral_eq]
  refine Eq.trans ?_ integral_conj
  simp [Circle.smul_def, conj_fourierChar]

/-- The more familiar specialization of `integral_inner_fourier_eq_integral_fourierInv_inner` to
`ℂ` -/
theorem Real.integral_fourierTransform_mul_eq_integral_mul_fourierTransform {f g : V → ℂ}
    (hf_int : Integrable f) (hg_int : Integrable g) :
    ∫ w, 𝓕 f w * g w = ∫ w, f w * 𝓕 g w := by
  have := integral_inner_fourier_eq_integral_fourierInv_inner
    (Complex.conjLIE.integrable_comp_iff.mpr hf_int) hg_int
  simp only [fourierIntegralInv_eq_fourierIntegral_neg] at this
  simp only [RCLike.inner_apply, conj_fourierIntegral] at this
  simpa using this.symm

/-- The Fourier transform preserves the L^2 norm, specialized to `ℂ`-valued functions. -/
theorem Real.integral_normSq_fourierIntegral_eq_integral_normSq {f : V → ℂ}
    (hf_cont : Continuous f) (hf_int : Integrable f) (hf_int_fourier : Integrable (𝓕 f)) :
    ∫ ξ, Complex.normSq (𝓕 f ξ) = ∫ x, Complex.normSq (f x) := by
  have := integral_norm_sq_fourier_eq_integral_norm_sq hf_cont hf_int hf_int_fourier
  simpa [Complex.normSq_eq_abs] using this

end Scalar

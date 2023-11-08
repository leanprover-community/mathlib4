/-
Copyright (c) 2023 Alex Kontorovich and Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Kontorovich, Heather Macbeth
-/

import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The Fourier transform of a Schwartz function is Schwartz
-/

open MeasureTheory RealInnerProductSpace Complex Real

variable (E F : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]

noncomputable section

abbrev integralFourier (f : SchwartzMap E F) := (VectorFourier.fourierIntegral (E := F)) Real.fourierChar (volume : Measure E) (innerₛₗ ℝ) f

-- belongs in Mathlib.Analysis.InnerProductSpace.Calculus
-- TODO : Add after `HasFDerivAt.inner`
theorem hasFDerivAt_inner (𝕜 : Type*) {E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] (v : E) (x : E) : HasFDerivAt (inner (𝕜 := 𝕜) v)
    (innerSL 𝕜 v) x := (innerSL 𝕜 v).hasFDerivAt

-- theorem : applying a continuous linear map to a schwartz map gives a schwartz map

-- collection of little lemmas about Schwartz maps

-- bub a Schwartz with a polynomial growth scalar is Schwartz

-- don't pull out f_hat on its own
def f_hat (f : SchwartzMap E ℂ) (x : E) : SchwartzMap E (E →L[ℝ] ℂ) := {
    toFun := fun v ↦ f v • (Complex.ofRealClm ∘L (innerSL ℝ) v)
    smooth' := by
      sorry
    decay' := by
      sorry
  }

def FourierDeriv (f : SchwartzMap E ℂ) (x : E) : (E →L[ℝ] ℂ) := by
  have f_hat : SchwartzMap E (E →L[ℝ] ℂ) := {
      toFun := fun v ↦ f v • (Complex.ofRealClm ∘L (innerSL ℝ) v)
      smooth' := by
        sorry
      decay' := by
        sorry
    }
  exact integralFourier E (E →L[ℝ] ℂ) f_hat x

-- where
--   toFun := by
--     intro u
--     let f_hat : SchwartzMap E ℂ := {
--       toFun := fun v ↦ ⟪v, u⟫_ℝ • f v
--       smooth' := by
--         sorry
--       decay' := by
--         sorry
--     }
--     exact -(2 * π * I) * integralFourier E ℂ f_hat x

--     --  fun v w : E ↦
--     -- ((-(2 * π * I * Real.fourierChar (-⟪w,v⟫_ℝ))) * (f v)) • (Complex.ofRealClm ∘L (innerSL ℝ) v)
--   map_add' := by
--     sorry
--   map_smul' := by
--     sorry
--   cont := by
--     sorry


-- theorem hasFDerivAt_inner' {E : Type*} [NormedAddCommGroup E]
--     [InnerProductSpace ℝ E] (v : E) (x : E) : HasFDerivAt (𝕜 := ℝ) (fun w : E ↦ ⟪w,v⟫_ℝ)
--     (innerSL ℝ v) x := by
--   convert (innerSL ℝ v).hasFDerivAt using 2 with w
--   rw [real_inner_comm]
--   rfl

/-
I think what's going wrong here is the following.

We just proved above that the derivative of `inner v := fun w ↦ ⟪v,w⟫` is itself. I think we need
the fact that the derivative of `inner' v := fun w ↦ ⟪w,v⟫` is, over ℝ, also `inner v`.??

The integral defining the FT is :
  `∫ v, e[-L v w] • f v ∂μ`
This is an integral over v of the function
  `F : v w ↦ e[-⟪v, w⟫] • f v`

The derivative *in w* is thus:
  `F' : v w ↦ (-2 π I) e(-⟪v, w⟫) • f v • (ContinuousLinear : u ↦ ⟪u, w⟫)`

whereas the "natural" thing we have access to is `innerSL`. If we put there `innerSL w`, then
we'll have the map
  `F' : v w ↦ (-2 π I) e(-⟪v, w⟫) • f v • (ContinuousLinear : u ↦ ⟪w, u⟫)`

So the theorems we're calling for this are getting the wrong variable...???

But if we put the variables the other way around, the derivative isn't right...
-/
theorem hasFDerivAt_fourier (f : SchwartzMap E ℂ) (x : E) :
    HasFDerivAt (integralFourier E ℂ f)
      (FourierDeriv E f x) x := by
  dsimp [integralFourier, FourierDeriv]
  let F' := fun v w : E ↦
    ((-(2 * π * I * Real.fourierChar (-⟪w,v⟫_ℝ))) * (f v)) • (Complex.ofRealClm ∘L (innerSL ℝ) v)


  convert (@hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (ε_pos := (by norm_num : (0:ℝ) < 1)) (α := E) (H := E) (E := ℂ) _ volume _ _ _ _ _ _
    _ _ F' x ?_ ?_ ?_ ?_ ?_ ?_ ?_)


  · simp only [FourierDeriv, neg_mul, real_smul, fourierChar, Multiplicative.toAdd,
    Multiplicative.ofAdd_symm_eq, MonoidHom.coe_mk, OneHom.coe_mk, expMapCircle_apply, ofReal_mul,
    ofReal_ofNat, neg_smul]
    calc _ = (∫ (v : E), (-(2 * π * I)) * (cexp (2 * π * (((innerₛₗ ℝ) v) x) * I))⁻¹ * f v) •
              ofRealClm.comp ((innerSL ℝ) x) := ?_
        _ = ∫ (v : E), ((-(2 * π * I) * (cexp (2 * π * (((innerₛₗ ℝ) v) x) * I))⁻¹ * f v)) •
              ofRealClm.comp ((innerSL ℝ) x) := by rw [integral_smul_const]
        _ = _ := ?_
    · rw [← @integral_mul_left]
      congr! 2
      ext1 y
      ring
    · congr! 1
      ext1 y
      --rw [real_inner_comm]
      rw [← Complex.exp_neg]
      simp only [innerₛₗ_apply, Multiplicative.toAdd, Multiplicative.ofAdd, Equiv.coe_fn_symm_mk,
        ofReal_neg, mul_neg, neg_mul]


-- #exit

--     have := @integral_smul_const

-- #exit

--     simp [ContinuousLinearMap.integral_comp_comm]
--     have : Integrable (fun v ↦
--       ((fourierChar (Multiplicative.ofAdd (((innerₛₗ ℝ) v) x))⁻¹) * f v) •
--     ContinuousLinearMap.comp ofRealClm ((innerSL ℝ) x)) (volume : Measure E) := sorry

--     have := ((1 : ℝ →L[ℝ] ℂ).smulRight (2 * π * I)).integral_comp_comm this

-- #exit

-- have := @integral_const_mul

--     simp only [map_inv, coe_inv_unitSphere, neg_mul, neg_smul]
--     -- rw [integral_smul_const]
--     -- congr! 5
--     sorry
--     -- rw [innerₛₗ_apply, real_inner_comm]
--     -- rfl
  · sorry
  · filter_upwards [] with a
    sorry -- AEStronglyMeasurable
  · -- integrable |f|
    sorry
  · sorry -- AEStronglyMeasurable
  · filter_upwards [] with w
    intro v hv
    dsimp
    sorry -- actual math!
  · sorry -- integrability of the bound
  · -- checking the derivative formula
    filter_upwards [] with w
    intro u hu
    convert (((Complex.ofRealClm.hasFDerivAt.comp u (hasFDerivAt_inner ℝ w u)).const_mul (2 * π)).mul_const I).neg.cexp.mul_const (f w) using 1
    · ext1 y
      simp only [fourierChar, ofAdd_neg, map_inv, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
        coe_inv_unitSphere, expMapCircle_apply, ofReal_mul, ofReal_ofNat, smul_eq_mul,
        Function.comp_apply, ofRealClm_apply]
      rw [Complex.exp_neg]
      rfl
    · simp only [fourierChar, Multiplicative.toAdd, Multiplicative.ofAdd, Equiv.coe_fn_symm_mk,
      MonoidHom.coe_mk, OneHom.coe_mk, mul_neg, expMapCircle_neg, coe_inv_unitSphere,
      expMapCircle_apply, ofReal_mul, ofReal_ofNat, neg_mul, neg_smul, Function.comp_apply,
      ofRealClm_apply, ← mul_smul, smul_neg, neg_inj]
      congr! 1
      rw [real_inner_comm]
      rw [Complex.exp_neg]
      ring_nf





#exit

    dsimp
    have h :
      HasFDerivAt (fun y : E ↦ ((fourierChar (Multiplicative.ofAdd (((innerₛₗ ℝ) w) y))⁻¹) : ℂ))
      (((fourierChar (↑(- inner v w : ℝ)))) • ContinuousLinearMap.comp ofRealClm ((innerSL ℝ) v)) v
    · simp only [fourierChar, expMapCircle, ContinuousMap.coe_mk, ofReal_mul, ofReal_ofNat,
      innerₛₗ_apply, map_inv, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, coe_inv_unitSphere]
      -- change HasFDerivAt (fun y ↦ (cexp (2 * π * (inner w y : ℝ) * I))⁻¹)
      --   (cexp (2 * π * (Multiplicative.toAdd (-inner v w : ℝ)) * I) •
      --   ContinuousLinearMap.comp ofRealClm ((innerSL ℝ) v)) v


      --have' := (hasFDerivAt_inner ℝ w v).ofReal_comp
--      have' := (((hasFDerivAt_inner ℝ w v).ofReal_comp (const_mul (2 * π))).mul_const (I : ℂ)).exp
      sorry
    convert h.mul_const (f w) using 1
    rw [mul_comm, mul_smul]
    congr!





  sorry

  -- let F' : E → E → E →L[ℝ] ℂ := ((innerFourier E f x) • (Complex.ofRealClm ∘L (innerSL ℝ)))

  -- refine (@hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
  --   (ε_pos := (by norm_num : (0:ℝ) < 1)) (α := E) (H := E) (E := ℂ) _ volume _ _ _ _ _ _
  --   _ _ ((innerFourier E f x) • (Complex.ofRealClm ∘L (innerSL ℝ) x)) x ?_ ?_ ?_ ?_ ?_ ?_ ?_) using 1



#exit

def SchwartzMap.fourierTransform (f : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := VectorFourier.fourierIntegral Real.fourierChar (volume : Measure E) (innerₛₗ ℝ) f
  smooth' := by
      refine contDiff_top.mpr ?_
      intro n
      have : n = 1 := by sorry
      rw [this]
      norm_cast
      refine contDiff_one_iff_fderiv.mpr ?_
      constructor
      · intro x
        refine (@hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
          (ε_pos := (by norm_num : (0:ℝ) < 1)) (α := E) (H := E) (E := ℂ) _ volume _ _ _ _ _ _
          _ _ ?_ x ?_ ?_ ?_ ?_ ?_ ?_ ?_).differentiableAt
        ·
      · sorry


  decay' := _

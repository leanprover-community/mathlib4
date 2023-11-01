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

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [FiniteDimensional ℝ E]

noncomputable section

abbrev innerFourier (f : SchwartzMap E ℂ) := (VectorFourier.fourierIntegral (E := ℂ)) Real.fourierChar (volume : Measure E) (innerₛₗ ℝ) f

-- belongs in Mathlib.Analysis.InnerProductSpace.Calculus
-- TODO : Add after `HasFDerivAt.inner`
theorem hasFDerivAt_inner (𝕜 : Type*) {E : Type*} [IsROrC 𝕜] [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [NormedSpace ℝ E] (v : E) (x : E) : HasFDerivAt (inner (𝕜 := 𝕜) v)
    (innerSL 𝕜 v) x := (innerSL 𝕜 v).hasFDerivAt


theorem hasFDerivAt_fourier (f : SchwartzMap E ℂ) (x : E) :
    HasFDerivAt (innerFourier E f)
      ((2 * π * I * innerFourier E f x) • (Complex.ofRealClm ∘L (innerSL ℝ) x)) x := by
  dsimp [innerFourier]
  have := ((innerFourier E f x) • (Complex.ofRealClm ∘L (innerSL ℝ x : E →L[ℝ] ℝ)))
  let F' := fun v w : E ↦
    ((-(2 * π * I * Real.fourierChar (-⟪v,w⟫_ℝ))) * (f w)) • (Complex.ofRealClm ∘L (innerSL ℝ) w)
  convert (@hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ)
    (ε_pos := (by norm_num : (0:ℝ) < 1)) (α := E) (H := E) (E := ℂ) _ volume _ _ _ _ _ _
    _ _ F' x ?_ ?_ ?_ ?_ ?_ ?_ ?_)
  · dsimp [VectorFourier.fourierIntegral]
    -- rw [@integral_smul_const]
    -- congr! 5
    sorry
    -- rw [innerₛₗ_apply, real_inner_comm]
    -- rfl
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
    intro v hv
    convert (((Complex.ofRealClm.hasFDerivAt.comp v (hasFDerivAt_inner ℝ w v)).const_mul (2 * π)).mul_const I).neg.cexp.mul_const (f w) using 1
    · ext1 y
      simp only [fourierChar, ofAdd_neg, map_inv, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
        coe_inv_unitSphere, expMapCircle_apply, ofReal_mul, ofReal_ofNat, smul_eq_mul,
        Function.comp_apply, ofRealClm_apply]
      rw [Complex.exp_neg]
      rfl
    · simp only [fourierChar, MonoidHom.coe_mk, OneHom.coe_mk, expMapCircle_apply, ofReal_mul,
      ofReal_ofNat, Function.comp_apply, ofRealClm_apply, smul_neg]
      simp only [Multiplicative.toAdd, Multiplicative.ofAdd, Equiv.coe_fn_symm_mk, ofReal_neg,
        mul_neg, neg_mul, neg_smul, ← mul_smul, neg_inj]
      congr! 1
      rw [real_inner_comm]
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

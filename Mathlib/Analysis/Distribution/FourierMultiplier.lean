/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.TemperedDistribution

/-!

# Fourier multiplier

-/


open SchwartzMap ContinuousLinearMap
open MeasureTheory MeasureTheory.Measure
open scoped FourierTransform

open scoped Nat NNReal ContDiff

variable {𝕜 𝕜' H D E F G V : Type*}

variable [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup H] [NormedAddCommGroup V]

variable --[NormedSpace ℝ E] [NormedSpace 𝕜 E]
  [NormedSpace ℂ E] [NormedSpace 𝕜 E] [SMulCommClass ℂ 𝕜 E]
  [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
  [MeasurableSpace H] [BorelSpace H]
  [NormedSpace 𝕜 V] [CompleteSpace E]



variable (f : 𝓢'(𝕜, H, E, V)) (g : H → 𝕜) (hg : g.HasTemperateGrowth)

#check _root_.smulLeftCLM V hg (E := E)
#check _root_.fourierTransformCLM

noncomputable
def fourierMultiplierCLM {g : H → 𝕜} (hg : g.HasTemperateGrowth) : 𝓢(H, E) →L[𝕜] 𝓢(H, E) :=
    (fourierTransformCLE 𝕜).symm.toContinuousLinearMap ∘L (smulLeftCLM E hg) ∘L
      (fourierTransformCLM 𝕜)

--@[simp]
theorem fourierMultiplierCLM_apply_apply {g : H → 𝕜} (hg : g.HasTemperateGrowth) (f : 𝓢(H, E)) (x : H) :
    fourierMultiplierCLM hg f x = 𝓕⁻ (g • 𝓕 f) x := by
  unfold fourierMultiplierCLM
  simp only [coe_comp', ContinuousLinearEquiv.coe_coe, Function.comp_apply,
    fourierTransformCLM_apply, fourierTransformCLE_symm_apply, fourierTransformInv_apply]
  congr

theorem fourierMultiplierCLM_const_apply (f : 𝓢(H, E)) :
    fourierMultiplierCLM (Function.HasTemperateGrowth.const (1 : 𝕜)) f = f := by
  --ext x
  unfold fourierMultiplierCLM
  simp
  sorry

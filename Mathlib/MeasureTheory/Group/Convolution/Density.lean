/-
Copyright (c) 2025 Miyahara Kō. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miyahara Kō
-/
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Group.Convolution

/-!
# PDF of convolution measures
-/

open MeasureTheory Measure Set Filter

open scoped NNReal Convolution

lemma MeasureTheory.Measure.withDensity_conv
    {f g : ℝ → ℝ} (hfn : 0 ≤ f) (hgn : 0 ≤ g) (hfm : Measurable f) (hgm : Measurable g)
    (hi : ∀ x, Integrable (fun y => f y * g (x - y))) :
    (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (f x)) ∗
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal (g x)) =
        (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal ((f ⋆ g) x)) := by
  classical
  ext s hs
  simp only [conv, convolution, ContinuousLinearMap.lsmul_apply, smul_eq_mul, hs, withDensity_apply]
  rw [map_apply (by fun_prop) hs, prod_withDensity (by fun_prop) (by fun_prop),
    withDensity_apply _ (hs.preimage (by fun_prop)),
    ← lintegral_indicator (hs.preimage (by fun_prop)) _,
    lintegral_prod _ (Measurable.aemeasurable
      (Measurable.indicator (by fun_prop) (hs.preimage (by fun_prop))))]
  conv => enter [1, 2, x]; rw [← lintegral_sub_right_eq_self _ x]
  conv =>
    enter [1, 2, x, 2, y]
    simp only [indicator, mem_preimage, add_sub_cancel]
    change s.indicator (fun y => ENNReal.ofReal (f x) * ENNReal.ofReal (g (y - x))) y
  conv => enter [1, 2, x]; rw [lintegral_indicator hs]
  conv =>
    enter [2, 2, x]
    rw [ofReal_integral_eq_lintegral_ofReal (hi x)
      (Eventually.of_forall (fun y => mul_nonneg (hfn y) (hgn (x - y))))]
    enter [2, y]
    rw [ENNReal.ofReal_mul (hfn y)]
  rw [lintegral_lintegral_swap (by fun_prop)]

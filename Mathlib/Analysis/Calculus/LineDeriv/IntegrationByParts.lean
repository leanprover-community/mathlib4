/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import Mathlib.Analysis.Calculus.LineDeriv.Measurable
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory Measure

/-- **Integration by parts for line derivatives**
Version with a general bilinear form `B`.
If `B f g` is integrable, as well as `B f' g` and `B f g'` where `f'` and `g'` are derivatives
of `f` and `g` in a given direction `v`, then `∫ B f' g = - ∫ B f g'`. -/
lemma fou {E F G W : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup W]
    [NormedSpace ℝ W] [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsAddHaarMeasure μ]
    {f f' : E → F} {g g' : E → G} {v : E} {B : F →L[ℝ] G →L[ℝ] W}
    (hf'g : Integrable (fun x ↦ B (f' x) (g x)) μ) (hfg' : Integrable (fun x ↦ B (f x) (g' x)) μ)
    (hfg : Integrable (fun x ↦ B (f x) (g x)) μ)
    (hf : ∀ x, HasLineDerivAt ℝ f (f' x) x v) (hg : ∀ x, HasLineDerivAt ℝ g (g' x) x v) :
    ∫ x, B (f' x) (g x) ∂μ = - ∫ x, B (f x) (g' x) ∂μ := by
  by_cases hW : CompleteSpace W; swap
  · simp [integral, hW]
  rcases eq_or_ne v 0 with rfl|hv
  · have Hf' x : f' x = 0 := by
      simpa [(hasLineDerivAt_zero (f := f) (x := x)).lineDeriv] using (hf x).lineDeriv.symm
    have Hg' x : g' x = 0 := by
      simpa [(hasLineDerivAt_zero (f := g) (x := x)).lineDeriv] using (hg x).lineDeriv.symm
    simp [Hf', Hg']

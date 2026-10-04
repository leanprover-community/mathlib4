/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic

/-!
# Lipschitz smoothness via the Fréchet derivative

Fréchet-derivative restatements of the `LipschitzSmoothWith` predicate for
`f : E → F`. For differentiable `f`, `lineDeriv ℝ f x v = fderiv ℝ f x v`
pointwise, and the predicate is equivalent to the two-sided Taylor bound stated
in `fderiv` form. The one-sided descent bounds require an order on the codomain
and are stated for real-valued `f` in a dedicated section.

This file also defines the segment-pointwise predicate `LipschitzSmoothOnSegmentWith` and
proves the **descent lemma**: a differentiable function with `K`-Lipschitz Fréchet derivative
is `K`-smooth. The proof integrates the segment-pointwise norm-bound along the segment from
`x` to `y` using the fundamental theorem of calculus.
-/

public section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : NNReal} {f : E → F}

theorem lipschitzSmoothWith_iff_fderiv (hf : Differentiable ℝ f) : LipschitzSmoothWith K f ↔
    ∀ x y : E, ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 := by
  rw [lipschitzSmoothWith_iff_lineDeriv]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [(hf x).lineDeriv_eq_fderiv]

namespace LipschitzSmoothWith

theorem fderiv_norm_le (h : LipschitzSmoothWith K f) (x y : E) (hf : DifferentiableAt ℝ f x) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_norm_le x y

theorem fderiv_apply_sub_norm_le (h : LipschitzSmoothWith K f) (x y : E)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    ‖fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x)‖ ≤ K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_norm_le x y

/-! ### Real-valued functions -/

section Real

variable {f : E → ℝ}

theorem fderiv_descent_le (h : LipschitzSmoothWith K f) (x y : E) (hf : DifferentiableAt ℝ f x) :
    f y ≤ f x + fderiv ℝ f x (y - x) + K / 2 * (dist x y) ^ 2 := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_le x y

theorem fderiv_descent_ge (h : LipschitzSmoothWith K f) (x y : E) (hf : DifferentiableAt ℝ f x) :
    f x + fderiv ℝ f x (y - x) - K / 2 * (dist x y) ^ 2 ≤ f y := by
  rw [← hf.lineDeriv_eq_fderiv]
  exact h.lineDeriv_descent_ge x y

theorem fderiv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : E)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K * (dist x y) ^ 2 := by
  rw [← hfy.lineDeriv_eq_fderiv, ← hfx.lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_le x y

theorem fderiv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : E)
    (hfx : DifferentiableAt ℝ f x) (hfy : DifferentiableAt ℝ f y) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K * (dist x y) ^ 2 := by
  rw [sub_apply]
  exact h.fderiv_apply_sub_le x y hfx hfy

end Real

end LipschitzSmoothWith

/-! ### Descent lemma -/

open AffineMap MeasureTheory

/-- The pointwise two-sided Lipschitz-smoothness bound on the Fréchet derivative along the
segment from `x` to `y`: `‖(fderiv ℝ f z - fderiv ℝ f x) (y - x)‖ ≤ K · dist x z · dist x y`
for all `z ∈ [x -[ℝ] y]`. This is the segment-pointwise form that integrates to the descent
inequality. -/
abbrev LipschitzSmoothOnSegmentWith (K : NNReal) (f : E → F) : Prop :=
  ∀ x y : E, ∀ z ∈ segment ℝ x y,
    ‖(fderiv ℝ f z - fderiv ℝ f x) (y - x)‖ ≤ K * dist x z * dist x y

/-- A `K`-Lipschitz Fréchet derivative implies the segment-pointwise smoothness bound.
Direct from the operator-norm bound (`ContinuousLinearMap.le_opNorm`) plus the Lipschitz bound
at the pair `(z, x)`. -/
theorem LipschitzSmoothOnSegmentWith.of_lipschitzWith_fderiv
    (hL : LipschitzWith K (fderiv ℝ f)) : LipschitzSmoothOnSegmentWith K f := fun x y z _ =>
  calc ‖(fderiv ℝ f z - fderiv ℝ f x) (y - x)‖
      ≤ ‖fderiv ℝ f z - fderiv ℝ f x‖ * ‖y - x‖ := ContinuousLinearMap.le_opNorm _ _
    _ = dist (fderiv ℝ f x) (fderiv ℝ f z) * dist x y := by simp only [← dist_eq_norm']
    _ ≤ K * dist x z * dist x y := mul_le_mul_of_nonneg_right (hL.dist_le_mul _ _) dist_nonneg

/-- For a segment-pointwise Lipschitz-smooth function with continuous Fréchet derivative, the
norm of the curve integral of `fderiv ℝ f z - fderiv ℝ f x` along the segment is
bounded by `K/2 · (dist x y)²`. The quantitative FTC step of the descent lemma. -/
theorem LipschitzSmoothOnSegmentWith.curveIntegral_norm_le
      (h : LipschitzSmoothOnSegmentWith K f) (hcont : Continuous (fderiv ℝ f)) (x y : E) :
      ‖∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x)‖ ≤ K / 2 * (dist x y) ^ 2 := by
  have h_integrable : IntervalIntegrable
      (fun t => (fderiv ℝ f (lineMap x y t) - fderiv ℝ f x) (y - x)) volume 0 1 :=
    curveIntegrable_segment.mp <|
      (hcont.curveIntegrable_segment).sub (curveIntegrable_segment_const _ x y)
  calc ‖∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x)‖
    _ = ‖∫ t in (0:ℝ)..1, (fderiv ℝ f (lineMap x y t) - fderiv ℝ f x) (y - x)‖ := by
        rw [curveIntegral_segment]
    _ ≤ ∫ t in (0:ℝ)..1, ‖(fderiv ℝ f (lineMap x y t) - fderiv ℝ f x) (y - x)‖ :=
        intervalIntegral.norm_integral_le_integral_norm zero_le_one
    _ ≤ ∫ t in (0:ℝ)..1, K * (dist x y) ^ 2 * t :=
        intervalIntegral.integral_mono_on zero_le_one h_integrable.norm
          (Continuous.intervalIntegrable (by fun_prop) _ _) (fun t ht =>
            (h _ _ _ (segment_eq_image_lineMap ℝ x y ▸ Set.mem_image_of_mem _ ht)).trans_eq <| by
              rw [dist_left_lineMap, Real.norm_of_nonneg ht.1]; ring)
    _ = K * (dist x y) ^ 2 * ∫ t in (0:ℝ)..1, t := intervalIntegral.integral_const_mul _ _
    _ = K / 2 * (dist x y) ^ 2 := by rw [integral_id]; ring

/-- The segment-pointwise smoothness bound, together with differentiability and continuity of
the Fréchet derivative, implies `K`-smoothness. The proof integrates the pointwise norm bound
along the segment from `x` to `y` using FTC. -/
theorem LipschitzSmoothOnSegmentWith.lipschitzSmoothWith [CompleteSpace F]
    (hptwise : LipschitzSmoothOnSegmentWith K f) (hf : Differentiable ℝ f)
    (hcont : Continuous (fderiv ℝ f)) : LipschitzSmoothWith K f := by
  refine lipschitzSmoothWith_iff_lineDeriv.mpr fun x y => ?_
  have heq : f y - f x - lineDeriv ℝ f x (y - x) =
      ∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x) := calc
    _ = f y - f x - (fderiv ℝ f x) (y - x) := by rw [(hf x).lineDeriv_eq_fderiv]
    _ = (∫ᶜ z in .segment x y, fderiv ℝ f z) - ∫ᶜ _ in .segment x y, fderiv ℝ f x := by
        rw [← curveIntegral_fderiv_segment (fun z _ => hf z) hcont.continuousOn,
          ← curveIntegral_segment_const]
    _ = ∫ᶜ z in .segment x y, (fderiv ℝ f z - fderiv ℝ f x) :=
        (curveIntegral_fun_sub (hcont.curveIntegrable_segment)
          (curveIntegrable_segment_const _ x y)).symm
  rw [heq]
  exact hptwise.curveIntegral_norm_le hcont x y

/-- **Descent lemma.** If `f` is differentiable and its Fréchet derivative is
`K`-Lipschitz, then `f` is `K`-smooth (without convexity assumption). -/
theorem Differentiable.lipschitzSmoothWith_of_lipschitzWith [CompleteSpace F]
    (hf : Differentiable ℝ f) (hL : LipschitzWith K (fderiv ℝ f)) : LipschitzSmoothWith K f :=
  (LipschitzSmoothOnSegmentWith.of_lipschitzWith_fderiv hL).lipschitzSmoothWith hf hL.continuous

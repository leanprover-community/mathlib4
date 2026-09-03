/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv

/-!
# Lipschitz smoothness in one dimension

For `f : 𝕜 → F`, the Fréchet-derivative formulation of Lipschitz smoothness reduces to the usual
derivative bound

`‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2`.
-/

public section

variable {𝕜 F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
variable {K : NNReal} {f : 𝕜 → F}

theorem lipschitzSmoothWith_iff_deriv :
    LipschitzSmoothWith 𝕜 K f ↔
      ∀ x y : 𝕜,
        ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothWith_iff_fderiv]
  simp only [fderiv_eq_smul_deriv, dist_eq_norm, norm_sub_rev]

theorem lipschitzSmoothOnWith_iff_derivWithin {s : Set 𝕜} (hs : UniqueDiffOn 𝕜 s) :
    LipschitzSmoothOnWith 𝕜 K f s ↔ DifferentiableOn 𝕜 f s ∧
      ∀ x ∈ s, ∀ y ∈ s,
        ‖f y - f x - (y - x) • derivWithin f s x‖ ≤ K / 2 * ‖y - x‖ ^ 2 := by
  rw [lipschitzSmoothOnWith_iff_fderivWithin hs]
  simp only [← toSpanSingleton_derivWithin, ContinuousLinearMap.toSpanSingleton_apply,
    dist_eq_norm, norm_sub_rev]

namespace LipschitzSmoothWith

theorem deriv_norm_le (h : LipschitzSmoothWith 𝕜 K f) (x y : 𝕜) :
    ‖f y - f x - (y - x) • deriv f x‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  lipschitzSmoothWith_iff_deriv.mp h x y

end LipschitzSmoothWith

namespace LipschitzSmoothOnWith

variable {s : Set 𝕜}

/-- The defining within-set quadratic bound in terms of `derivWithin`. -/
theorem derivWithin_norm_le (h : LipschitzSmoothOnWith 𝕜 K f s)
    (hs : UniqueDiffOn 𝕜 s) {x y : 𝕜} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - (y - x) • derivWithin f s x‖ ≤ K / 2 * ‖y - x‖ ^ 2 :=
  (lipschitzSmoothOnWith_iff_derivWithin hs).mp h |>.2 x hx y hy

end LipschitzSmoothOnWith

/-! ### Real-valued functions -/

namespace LipschitzSmoothWith

variable {K : NNReal} {f : ℝ → ℝ}

theorem deriv_descent_le (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    f y ≤ f x + deriv f x * (y - x) + K / 2 * (y - x) ^ 2 := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_le x y

theorem deriv_descent_ge (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    f x + deriv f x * (y - x) - K / 2 * (y - x) ^ 2 ≤ f y := by
  simpa only [fderiv_eq_deriv_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_descent_ge x y

theorem deriv_sub_mul_le (h : LipschitzSmoothWith ℝ K f) (x y : ℝ) :
    (deriv f y - deriv f x) * (y - x) ≤ K * (y - x) ^ 2 := by
  simpa only [sub_apply, fderiv_eq_deriv_mul, ← sub_mul, dist_comm x y, Real.dist_eq, sq_abs]
    using h.fderiv_sub_apply_le x y

end LipschitzSmoothWith

namespace LipschitzSmoothOnWith

variable {K : NNReal} {f : ℝ → ℝ} {s : Set ℝ}

/-- The quadratic upper bound on `f y` within a set, in terms of `derivWithin`. -/
theorem derivWithin_descent_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    f y ≤ f x + derivWithin f s x * (y - x) + K / 2 * (y - x) ^ 2 := by
  simpa [← toSpanSingleton_derivWithin, mul_comm, dist_comm x y, Real.dist_eq, sq_abs] using
    h.fderivWithin_descent_le hs hx hy

/-- The quadratic lower bound on `f y` within a set, in terms of `derivWithin`. -/
theorem derivWithin_descent_ge (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    f x + derivWithin f s x * (y - x) - K / 2 * (y - x) ^ 2 ≤ f y := by
  simpa [← toSpanSingleton_derivWithin, mul_comm, dist_comm x y, Real.dist_eq, sq_abs] using
    h.fderivWithin_descent_ge hs hx hy

/-- One-sided bound on the variation of `derivWithin`. -/
theorem derivWithin_sub_mul_le (h : LipschitzSmoothOnWith ℝ K f s)
    (hs : UniqueDiffOn ℝ s) {x y : ℝ} (hx : x ∈ s) (hy : y ∈ s) :
    (derivWithin f s y - derivWithin f s x) * (y - x) ≤ K * (y - x) ^ 2 := by
  rw [mul_comm (derivWithin f s y - derivWithin f s x)]
  simpa only [← toSpanSingleton_derivWithin, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, ← mul_sub, dist_comm x y, Real.dist_eq, sq_abs] using
    h.fderivWithin_apply_sub_le hs hx hy

end LipschitzSmoothOnWith

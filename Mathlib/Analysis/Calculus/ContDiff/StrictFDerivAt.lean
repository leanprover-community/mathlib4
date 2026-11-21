/-
Copyright (c) 2026 Michael Rothgang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Rothgang
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Higher differentiability over general non-trivially normed fields

In this file, we prove a general criterion for a derivative being a strict derivative:
this is true when the function is `C¹` around a point (over the real or complex numbers),
and if the function is analytic near the point (over any field).
-/

open scoped ContDiff

public section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  {n : ℕ∞ω}

/-- If a function is `C^n` around a point (with `minSmoothness 𝕜 1 ≤ n`),
the derivative of `f` at this point is also a strict derivative.

See `ContDiffAt.hasStrictFDerivAt_fderiv` for a version specialised `ℝ` or `ℂ`,
which only requires `1 ≤ n`.
-/
lemma ContDiffAt.hasStrictFDerivAt_fderiv_of_minSmoothness_le {f : E₁ → E₂} {p : E₁}
    (hf : ContDiffAt 𝕜 n f p) (hn : minSmoothness 𝕜 1 ≤ n) :
    HasStrictFDerivAt f (fderiv 𝕜 f p) p := by
  by_cases! h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜:= h.rclike
    rw [minSmoothness_of_isRCLikeNormedField] at hn
    exact hf.hasStrictFDerivAt_fderiv (ENat.one_le_iff_ne_zero_withTop.mp hn)
  · rw [eq_top_of_minSmoothness_le_of_not_isRCLikeNormedField h hn] at hf
    exact hf.analyticAt.hasStrictFDerivAt

/-- If a function is `C^n` around a point (with `minSmoothness 𝕜 1 ≤ n`),
the derivative of `f` at this point is also a strict derivative.

See `ContDiffAt.hasStrictFDerivAt` for a version specialised to `ℝ` or `ℂ`,
which only requires `1 ≤ n`.
-/
lemma ContDiffAt.hasStrictFDerivAt_of_minSmoothness_le
    {f : E₁ → E₂} {p : E₁} {f' : E₁ →L[𝕜] E₂} (hf : ContDiffAt 𝕜 n f p)
    (hf' : HasFDerivAt f f' p) (hn : minSmoothness 𝕜 1 ≤ n) :
    HasStrictFDerivAt f f' p := by
  rw [← hf'.fderiv]
  exact hf.hasStrictFDerivAt_fderiv_of_minSmoothness_le hn

/-- If a function is `C^n` around a point (with `minSmoothness 𝕜 1 ≤ n`),
the derivative of `f` at this point is also a strict derivative.

See `ContDiffAt.hasStrictDerivAt` for a version specialised to `ℝ` or `ℂ`,
which only requires `1 ≤ n`.
-/
lemma ContDiffAt.hasStrictDerivAt_deriv_of_minSmoothness_le
    {f : 𝕜 → E₂} {x : 𝕜} (hf : ContDiffAt 𝕜 n f x) (hn : minSmoothness 𝕜 1 ≤ n) :
    HasStrictDerivAt f (deriv f x) x := by
  by_cases! h : IsRCLikeNormedField 𝕜
  · let : RCLike 𝕜:= h.rclike
    rw [minSmoothness_of_isRCLikeNormedField] at hn
    exact hf.hasStrictDerivAt_deriv (ENat.one_le_iff_ne_zero_withTop.mp hn)
  · rw [eq_top_of_minSmoothness_le_of_not_isRCLikeNormedField h hn] at hf
    exact hf.analyticAt.hasStrictDerivAt

/-- If a function is `C^n` around a point (with `minSmoothness 𝕜 1 ≤ n`),
the derivative of `f` at this point is also a strict derivative.

See `ContDiffAt.hasStrictDerivAt` for a version specialised to `ℝ` or `ℂ`,
which only requires `1 ≤ n`.
-/
lemma ContDiffAt.hasStrictDerivAt_of_minSmoothness_le {f : 𝕜 → E₂} {x : 𝕜} {a : E₂}
    (hf : ContDiffAt 𝕜 n f x) (hf' : HasDerivAt f a x) (hn : minSmoothness 𝕜 1 ≤ n) :
    HasStrictDerivAt f a x := by
  rw [← hf'.deriv]
  exact hf.hasStrictDerivAt_deriv_of_minSmoothness_le hn

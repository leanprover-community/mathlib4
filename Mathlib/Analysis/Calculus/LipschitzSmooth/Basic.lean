/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Lipschitz smoothness

A real-valued function `f` on a normed real vector space is **`K`-smooth** if
it satisfies the quadratic descent inequality

`f y ≤ f x + lineDeriv ℝ f x (y - x) + (K / 2) (dist x y)²`

for all `x, y`. This is the standard quadratic upper bound used to control
descent steps in first-order convex optimisation. The `K / 2` convention
makes the descent lemma constant-preserving: a `K`-Lipschitz Fréchet
derivative implies `K`-smoothness.

The predicate is stated using `lineDeriv` so it does not presuppose Fréchet
differentiability; for differentiable `f`, `lineDeriv` and `fderiv` agree
pointwise. Fréchet-derivative restatements and the descent lemma — whose
hypothesis `LipschitzWith K (fderiv ℝ f)` lives in the fderiv world — are in
`Mathlib.Analysis.Calculus.LipschitzSmooth.FDeriv`. Inner-product-space restatements
via the gradient `∇` and `⟪·, ·⟫` are in
`Mathlib.Analysis.Calculus.LipschitzSmooth.Gradient`.

## Main definitions

* `LipschitzSmoothWith K f` — the predicate above.

## Main results

* `LipschitzSmoothWith.lineDeriv_apply_sub_le` — a `K`-smooth `f` satisfies
  the quadratic upper bound `lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)
  ≤ K · (dist x y)²` on the variation of its line-derivative, with no
  additional hypotheses.
* `LipschitzSmoothWith.lineDeriv_sub_apply_le` — the same bound stated with
  function-level subtraction, `(lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x)`.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real-valued function `f` on a normed real vector space `F` is `K`-smooth
if it satisfies the quadratic descent inequality
`f y ≤ f x + lineDeriv ℝ f x (y - x) + (K / 2) (dist x y)²` for all `x, y`. -/
@[expose] def LipschitzSmoothWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ (x y : F), f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2

namespace LipschitzSmoothWith

variable {K : NNReal} {f : F → ℝ}

/-- A `K`-smooth `f` satisfies a quadratic upper bound on the variation of its line-derivative:
`lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ K · (dist x y)²`. -/
theorem lineDeriv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : F) :
    lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  linarith [h x y, lineDeriv_neg (𝕜 := ℝ) (f := f) ▸ neg_sub y _ ▸ dist_comm y _ ▸ h y x]

/-- Function-subtraction restatement of `lineDeriv_apply_sub_le`:
`(lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ K · (dist x y)²`. -/
theorem lineDeriv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : F) :
    (lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 :=
  Pi.sub_apply (lineDeriv ℝ f _) _ _ ▸ h.lineDeriv_apply_sub_le x y

end LipschitzSmoothWith

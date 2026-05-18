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

* `lipschitzSmoothWith_iff_lineDeriv` — characterisation in line-derivative form.
* `LipschitzSmoothWith.lineDeriv_descent_le` — the defining descent inequality
  extracted as a forward implication.
* `LipschitzSmoothWith.lineDeriv_apply_sub_le` — a `K`-smooth `f` satisfies the
  quadratic upper bound `lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ K · (dist x y)²`
  on the variation of its line-derivative, with no additional hypotheses.
* `LipschitzSmoothWith.lineDeriv_sub_apply_le` — function-subtraction restatement.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real-valued function `f` on a normed real vector space `F` is `K`-smooth
if it satisfies the quadratic descent inequality
`f y ≤ f x + lineDeriv ℝ f x (y - x) + (K / 2) (dist x y)²` for all `x, y`.

The choice of `lineDeriv` here is an implementation detail: it is the weakest form
that makes the predicate well-defined for non-differentiable functions. Equivalent
characterisations in `fderiv`, `gradient`, and `deriv` form are provided in the
sibling files, predicated on the appropriate differentiability hypothesis. -/
def LipschitzSmoothWith (K : NNReal) (f : F → ℝ) : Prop :=
  ∀ (x y : F), f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2

/-- Characterisation of `LipschitzSmoothWith` in line-derivative form. -/
theorem lipschitzSmoothWith_iff_lineDeriv {K : NNReal} {f : F → ℝ} :
    LipschitzSmoothWith K f ↔
      ∀ x y : F, f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 :=
  Iff.rfl

namespace LipschitzSmoothWith

variable {K : NNReal} {f : F → ℝ}

/-- The defining descent inequality of a `K`-smooth function in line-derivative form. -/
theorem lineDeriv_descent_le (h : LipschitzSmoothWith K f) (x y : F) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 :=
  h x y

/-- A `K`-smooth `f` satisfies a quadratic upper bound on the variation of its line-derivative:
`lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ K · (dist x y)²`. -/
theorem lineDeriv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : F) :
    lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  linarith [h.lineDeriv_descent_le x y,
    lineDeriv_neg (𝕜 := ℝ) (f := f) ▸ neg_sub y _ ▸ dist_comm y _ ▸ h.lineDeriv_descent_le y x]

/-- Function-subtraction restatement of `lineDeriv_apply_sub_le`:
`(lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ K · (dist x y)²`. -/
theorem lineDeriv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : F) :
    (lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 :=
  Pi.sub_apply (lineDeriv ℝ f _) _ _ ▸ h.lineDeriv_apply_sub_le x y

end LipschitzSmoothWith

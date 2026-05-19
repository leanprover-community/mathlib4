/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Lipschitz smoothness

A real-valued function `f` on a normed real vector space is **`K`-smooth** if it satisfies
the quadratic descent inequality

`f y ≤ f x + lineDeriv ℝ f x (y - x) + (K / 2) (dist x y)²`

for all `x, y`. The predicate uses `lineDeriv` so as not to presuppose Fréchet
differentiability; restatements in `fderiv`, 1D `deriv`, and Hilbert-space gradient
form live in the sibling files in this directory.

## Main definitions

* `LipschitzSmoothWith K f` — the predicate above.

## Main results

* `lipschitzSmoothWith_iff_lineDeriv` — characterisation as the underlying inequality.
* `LipschitzSmoothWith.lineDeriv_descent_le`, `LipschitzSmoothWith.lineDeriv_apply_sub_le`,
  `LipschitzSmoothWith.lineDeriv_sub_apply_le` — the descent inequality as a forward
  implication and the resulting variance bound on the line-derivative.
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
def LipschitzSmoothWith (K : NNReal) (f : F → ℝ) :=
  ∀ (x y : F), f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2

theorem lipschitzSmoothWith_iff_lineDeriv {K : NNReal} {f : F → ℝ} : LipschitzSmoothWith K f ↔
    ∀ x y : F, f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := Iff.rfl

namespace LipschitzSmoothWith

variable {K : NNReal} {f : F → ℝ}

theorem lineDeriv_descent_le (h : LipschitzSmoothWith K f) (x y : F) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := h x y

theorem lineDeriv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : F) :
    lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  have hyx := h.lineDeriv_descent_le y x
  rw [← neg_sub y x, lineDeriv_neg, dist_comm] at hyx
  linarith [h.lineDeriv_descent_le x y, hyx]

theorem lineDeriv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : F) :
    (lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 :=
  Pi.sub_apply (lineDeriv ℝ f _) _ _ ▸ h.lineDeriv_apply_sub_le x y

end LipschitzSmoothWith

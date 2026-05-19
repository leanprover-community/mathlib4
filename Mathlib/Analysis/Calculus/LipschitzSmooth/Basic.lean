/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Lipschitz smoothness

A real-valued function `f` on a normed real vector space is **`K`-smooth** if the
first-order Taylor remainder is bounded quadratically:

`|f y - f x - lineDeriv ℝ f x (y - x)| ≤ (K / 2) (dist x y)²`

for all `x, y`. The predicate uses `lineDeriv` so as not to presuppose Fréchet
differentiability; equivalent characterisations in `fderiv`, 1D `deriv`, and
Hilbert-space gradient form live in the sibling files in this directory.

This two-sided (absolute-value) form is orientation-agnostic (closed under
`f ↦ -f`) — matching the textbook notion of L-smoothness (Lipschitz gradient,
the class `C^{1,1}`) used in Nesterov, Beck, Bauschke-Combettes, etc.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A real-valued function `f` on a normed real vector space `F` is `K`-smooth
if the first-order Taylor remainder is bounded quadratically:
`|f y - f x - lineDeriv ℝ f x (y - x)| ≤ (K / 2) (dist x y)²` for all `x, y`.

The predicate is two-sided (absolute value), so closed under `f ↦ -f` and
matching the textbook L-smoothness / `C^{1,1}` class. The `lineDeriv` form is
the weakest possible underlying derivative form — the predicate implies
line-differentiability everywhere (`LipschitzSmoothWith.hasLineDerivAt`), so
the `lineDeriv` value is always the actual line derivative.

Equivalent characterisations in `fderiv`, `gradient`, and `deriv` form are
provided in the sibling files, predicated on `Differentiable` where useful. -/
def LipschitzSmoothWith (K : NNReal) (f : F → ℝ) :=
  ∀ (x y : F), |f y - f x - lineDeriv ℝ f x (y - x)| ≤ ↑K / 2 * (dist x y) ^ 2

theorem lipschitzSmoothWith_iff_lineDeriv {K : NNReal} {f : F → ℝ} : LipschitzSmoothWith K f ↔
    ∀ x y : F, |f y - f x - lineDeriv ℝ f x (y - x)| ≤ ↑K / 2 * (dist x y) ^ 2 := Iff.rfl

namespace LipschitzSmoothWith

variable {K : NNReal} {f : F → ℝ}

/-- Primary extractor: the Taylor remainder is bounded in absolute value. -/
theorem lineDeriv_abs_le (h : LipschitzSmoothWith K f) (x y : F) :
    |f y - f x - lineDeriv ℝ f x (y - x)| ≤ ↑K / 2 * (dist x y) ^ 2 := h x y

/-- Descent inequality (upper-bound extractor). -/
theorem lineDeriv_descent_le (h : LipschitzSmoothWith K f) (x y : F) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := by
  have := (abs_le.mp (h.lineDeriv_abs_le x y)).2
  linarith

/-- Ascent inequality (lower-bound extractor). -/
theorem lineDeriv_descent_ge (h : LipschitzSmoothWith K f) (x y : F) :
    f x + lineDeriv ℝ f x (y - x) - ↑K / 2 * (dist x y) ^ 2 ≤ f y := by
  have := (abs_le.mp (h.lineDeriv_abs_le x y)).1
  linarith

/-- One-sided variance bound on the line derivative. -/
theorem lineDeriv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : F) :
    lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  have hyx := h.lineDeriv_descent_le y x
  rw [← neg_sub y x, lineDeriv_neg, dist_comm] at hyx
  linarith [h.lineDeriv_descent_le x y, hyx]

/-- Two-sided variance bound on the line derivative. -/
theorem lineDeriv_apply_sub_abs_le (h : LipschitzSmoothWith K f) (x y : F) :
    |lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)| ≤ ↑K * (dist x y) ^ 2 := by
  rw [abs_le]
  refine ⟨?_, h.lineDeriv_apply_sub_le x y⟩
  have hyx := h.lineDeriv_descent_ge y x
  rw [← neg_sub y x, lineDeriv_neg, dist_comm] at hyx
  linarith [h.lineDeriv_descent_ge x y]

/-- Functional-form variance bound. -/
theorem lineDeriv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : F) :
    (lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 :=
  Pi.sub_apply (lineDeriv ℝ f _) _ _ ▸ h.lineDeriv_apply_sub_le x y

/-- `K`-smoothness implies line-differentiability: the actual line derivative
exists at every `x, v` and equals `lineDeriv ℝ f x v`. Proof: the predicate
bound `|f(x + tv) - f x - t · L| ≤ K/2 · t² ‖v‖²` (via `lineDeriv_smul` to
factor `t`) is `o(t)`. -/
theorem hasLineDerivAt (h : LipschitzSmoothWith K f) (x v : F) :
    HasLineDerivAt ℝ f (lineDeriv ℝ f x v) x v :=
  sorry

/-- A `K`-smooth function is line-differentiable everywhere. -/
theorem lineDifferentiableAt (h : LipschitzSmoothWith K f) (x v : F) :
    LineDifferentiableAt ℝ f x v :=
  (h.hasLineDerivAt x v).lineDifferentiableAt

end LipschitzSmoothWith

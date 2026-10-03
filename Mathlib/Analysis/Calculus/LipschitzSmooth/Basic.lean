/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic

/-!
# Lipschitz smoothness

A function `f : E → F` between real normed vector spaces is **`K`-smooth** if the
first-order Taylor remainder is bounded quadratically:

`‖f y - f x - lineDeriv ℝ f x (y - x)‖ ≤ (K / 2) * (dist x y) ^ 2`

for all `x, y`. The predicate uses `lineDeriv` so as not to presuppose Fréchet
differentiability; equivalent characterisations in `fderiv`, 1D `deriv`, and
Hilbert-space gradient form live in the sibling files in this directory.

This two-sided (norm) form is orientation-agnostic (closed under `f ↦ -f`) —
matching, for real-valued `f`, the textbook notion of L-smoothness (Lipschitz
gradient, the class `C^{1,1}`). The one-sided descent bounds require an order
on the codomain and are stated for real-valued `f` in a dedicated section.
-/

public section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A function `f : E → F` between real normed vector spaces is `K`-smooth
if the first-order Taylor remainder is bounded quadratically:
`‖f y - f x - lineDeriv ℝ f x (y - x)‖ ≤ (K / 2) * (dist x y) ^ 2` for all `x, y`.

The predicate is two-sided (norm), so closed under `f ↦ -f` and matching, for
real-valued `f`, the textbook L-smoothness / `C^{1,1}` class. The `lineDeriv`
form is the weakest possible underlying derivative form — the predicate implies
line-differentiability everywhere (`LipschitzSmoothWith.hasLineDerivAt`), so
the `lineDeriv` value is always the actual line derivative.

Equivalent characterisations in `fderiv`, `gradient`, and `deriv` form are
provided in the sibling files, predicated on `Differentiable` where useful.
The one-sided descent bounds, which require an order on the codomain, are
stated for real-valued `f`. -/
def LipschitzSmoothWith (K : NNReal) (f : E → F) :=
  ∀ (x y : E), ‖f y - f x - lineDeriv ℝ f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2

theorem lipschitzSmoothWith_iff_lineDeriv {K : NNReal} {f : E → F} : LipschitzSmoothWith K f ↔
    ∀ x y : E, ‖f y - f x - lineDeriv ℝ f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 := Iff.rfl

namespace LipschitzSmoothWith

variable {K : NNReal} {f : E → F}

/-- The two-sided quadratic bound on the first-order Taylor remainder, restated
from the definition for dot notation. -/
theorem lineDeriv_norm_le (h : LipschitzSmoothWith K f) (x y : E) :
    ‖f y - f x - lineDeriv ℝ f x (y - x)‖ ≤ K / 2 * (dist x y) ^ 2 := h x y

/-- Two-sided bound on the variation of the line derivative along `y - x`. -/
theorem lineDeriv_apply_sub_norm_le (h : LipschitzSmoothWith K f) (x y : E) :
    ‖lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x)‖ ≤ K * (dist x y) ^ 2 := by
  have hyx := h.lineDeriv_norm_le y x
  rw [← neg_sub y x, lineDeriv_neg, sub_neg_eq_add, dist_comm] at hyx
  have key := (norm_add_le _ _).trans (add_le_add hyx (h.lineDeriv_norm_le x y))
  rw [show f x - f y + lineDeriv ℝ f y (y - x) + (f y - f x - lineDeriv ℝ f x (y - x))
      = lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) from by abel] at key
  linarith

/-- `K`-smoothness implies line-differentiability: the actual line derivative
exists at every `x, v` and equals `lineDeriv ℝ f x v`. The predicate bound
`‖f (x + tv) - f x - t • L‖ ≤ K/2 · t² ‖v‖²` (via `lineDeriv_smul` to factor `t`)
is `o(t)`. -/
theorem hasLineDerivAt (h : LipschitzSmoothWith K f) (x v : E) :
    HasLineDerivAt ℝ f (lineDeriv ℝ f x v) x v := by
  set L := lineDeriv ℝ f x v
  change HasDerivAt (fun t : ℝ => f (x + t • v)) L 0
  rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  have hsum_pos : (0:ℝ) < K * ‖v‖^2 / 2 + 1 := by positivity
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (div_pos hε hsum_pos)] with t ht
  simp only [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
  simp only [zero_add, zero_smul, add_zero, Real.norm_eq_abs]
  have hpred := h x (x + t • v)
  rw [show (x + t • v) - x = t • v from by abel, lineDeriv_smul,
      dist_self_add_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at hpred
  refine hpred.trans ?_
  have ht' : |t| * (K * ‖v‖^2 / 2 + 1) < ε := (lt_div_iff₀ hsum_pos).mp ht
  have ht'' : K * ‖v‖^2 / 2 * |t| ≤ ε := by nlinarith [abs_nonneg t]
  calc K / 2 * (t ^ 2 * ‖v‖ ^ 2)
      = K * ‖v‖^2 / 2 * |t| * |t| := by rw [← sq_abs t]; ring
    _ ≤ ε * |t| := mul_le_mul_of_nonneg_right ht'' (abs_nonneg t)

/-- A `K`-smooth function is line-differentiable everywhere. -/
theorem lineDifferentiableAt (h : LipschitzSmoothWith K f) (x v : E) :
    LineDifferentiableAt ℝ f x v :=
  (h.hasLineDerivAt x v).lineDifferentiableAt

/-! ### Real-valued functions

The one-sided (order-based) bounds require an order on the codomain, so they are
stated for real-valued `f`. The norm and the absolute value agree on `ℝ`
(`Real.norm_eq_abs`), so the two-sided bounds above apply verbatim. -/

section Real

variable {f : E → ℝ}

/-- The quadratic upper bound on `f y`, traditionally called the *descent lemma*. -/
theorem lineDeriv_descent_le (h : LipschitzSmoothWith K f) (x y : E) :
    f y ≤ f x + lineDeriv ℝ f x (y - x) + K / 2 * (dist x y) ^ 2 := by
  linarith [(abs_le.mp (h.lineDeriv_norm_le x y)).2]

/-- The quadratic lower bound on `f y`: the descent lemma applied to `-f`. -/
theorem lineDeriv_descent_ge (h : LipschitzSmoothWith K f) (x y : E) :
    f x + lineDeriv ℝ f x (y - x) - K / 2 * (dist x y) ^ 2 ≤ f y := by
  linarith [(abs_le.mp (h.lineDeriv_norm_le x y)).1]

/-- One-sided bound on the variation of the line derivative along `y - x`. -/
theorem lineDeriv_apply_sub_le (h : LipschitzSmoothWith K f) (x y : E) :
    lineDeriv ℝ f y (y - x) - lineDeriv ℝ f x (y - x) ≤ K * (dist x y) ^ 2 :=
  le_of_abs_le (h.lineDeriv_apply_sub_norm_le x y)

/-- The one-sided variation bound in functional form: the difference of
line-derivative maps applied to `y - x`. -/
theorem lineDeriv_sub_apply_le (h : LipschitzSmoothWith K f) (x y : E) :
    (lineDeriv ℝ f y - lineDeriv ℝ f x) (y - x) ≤ K * (dist x y) ^ 2 :=
  Pi.sub_apply (lineDeriv ℝ f _) _ _ ▸ h.lineDeriv_apply_sub_le x y

end Real

end LipschitzSmoothWith

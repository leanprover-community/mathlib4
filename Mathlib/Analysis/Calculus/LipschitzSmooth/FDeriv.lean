/-
Copyright (c) 2026 Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christoph Spiegel
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Calculus.LipschitzSmooth.Basic

/-!
# Lipschitz smoothness via the Fréchet derivative

Fréchet-derivative restatements of the `LipschitzSmoothWith` predicate from
`Mathlib.Analysis.Calculus.LipschitzSmooth.Basic`. For differentiable `f`,
`lineDeriv ℝ f x v = fderiv ℝ f x v` pointwise, and the predicate is equivalent
to the corresponding descent inequality stated in `fderiv` form.

This file provides only the equivalence and the elementary variance-bound consequences;
the full descent lemma — i.e. the converse direction
`LipschitzWith K (fderiv ℝ f) → LipschitzSmoothWith K f` — is deferred to a follow-up.

## Main results

* `lipschitzSmoothWith_iff_fderiv` — characterisation of `K`-smoothness in Fréchet form
  under `Differentiable`.
* `LipschitzSmoothWith.fderiv_descent_le` — the descent inequality in Fréchet form.
* `LipschitzSmoothWith.fderiv_apply_sub_le` — variance bound on the Fréchet derivative,
  `fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K · (dist x y)²`.
* `LipschitzSmoothWith.fderiv_sub_apply_le` — function-subtraction restatement,
  `(fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K · (dist x y)²`.
-/

public section

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
variable {K : NNReal} {f : F → ℝ}

/-- Characterisation of `LipschitzSmoothWith` in Fréchet-derivative form, under
`Differentiable`. -/
theorem lipschitzSmoothWith_iff_fderiv (hf : Differentiable ℝ f) :
    LipschitzSmoothWith K f ↔
      ∀ x y : F, f y ≤ f x + fderiv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 := by
  rw [lipschitzSmoothWith_iff_lineDeriv]
  refine forall_congr' fun x => forall_congr' fun y => ?_
  rw [(hf x).lineDeriv_eq_fderiv]

namespace LipschitzSmoothWith

/-- The descent inequality of a `K`-smooth `f` in Fréchet-derivative form, under
`Differentiable`. -/
theorem fderiv_descent_le (h : LipschitzSmoothWith K f)
    (hf : Differentiable ℝ f) (x y : F) :
    f y ≤ f x + fderiv ℝ f x (y - x) + ↑K / 2 * (dist x y) ^ 2 :=
  (lipschitzSmoothWith_iff_fderiv hf).mp h x y

/-- For a differentiable `K`-smooth `f`, the variation of the Fréchet derivative satisfies
`fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ K · (dist x y)²`. -/
theorem fderiv_apply_sub_le (h : LipschitzSmoothWith K f) (hf : Differentiable ℝ f) (x y : F) :
    fderiv ℝ f y (y - x) - fderiv ℝ f x (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  rw [← (hf y).lineDeriv_eq_fderiv, ← (hf x).lineDeriv_eq_fderiv]
  exact h.lineDeriv_apply_sub_le x y

/-- Function-subtraction restatement of `fderiv_apply_sub_le`:
`(fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ K · (dist x y)²`. -/
theorem fderiv_sub_apply_le (h : LipschitzSmoothWith K f) (hf : Differentiable ℝ f) (x y : F) :
    (fderiv ℝ f y - fderiv ℝ f x) (y - x) ≤ ↑K * (dist x y) ^ 2 := by
  rw [ContinuousLinearMap.sub_apply]
  exact h.fderiv_apply_sub_le hf x y

end LipschitzSmoothWith

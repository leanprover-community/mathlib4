/-
Copyright (c) 2026 Allen Hao Zhu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Allen Hao Zhu
-/
module

public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Data.Real.Sign

/-!
# Subgradients of the absolute value and the `ℓ¹` norm

This file develops the elementary subgradient calculus for the real
absolute-value function `|·| : ℝ → ℝ` and its componentwise lift to the
`ℓ¹` norm `‖v‖₁ = ∑ᵢ |vᵢ|` on `Fin n → ℝ`.

A real number `g` is a subgradient of `|·|` at `x` when
`|y| ≥ |x| + g * (y - x)` holds for every `y : ℝ`. The classical
characterization (Boyd–Vandenberghe, §3.1.5; Hiriart-Urruty–Lemaréchal,
Vol. I, §VI.3) states that the subdifferential `∂|·|(x)` equals

* `{1}` if `x > 0`,
* `{-1}` if `x < 0`,
* `[-1, 1]` if `x = 0`.

These three cases unify via `Real.sign` away from `0`. Lifting
coordinate-by-coordinate yields the `ℓ¹` subdifferential, which is the
algebraic backbone of the Lasso KKT optimality system.

## Main definitions

* `Convex.IsAbsSubgradient`: predicate stating that a real `g` is a
  subgradient of `|·|` at `x`.
* `Convex.IsL1Subgradient`: componentwise lift of `IsAbsSubgradient` to
  `Fin n → ℝ`.

## Main results

* `Convex.isAbsSubgradient_of_pos`, `Convex.isAbsSubgradient_of_neg`:
  the constants `1` and `-1` are subgradients at strictly positive and
  strictly negative inputs, respectively.
* `Convex.isAbsSubgradient_zero_iff`: the subdifferential at `0` is
  exactly the closed interval `[-1, 1]`.
* `Convex.isAbsSubgradient_sign`: `Real.sign x` is a subgradient at
  every nonzero `x` (it is in fact the unique one).
* `Convex.abs_subgradient_mem_interval`: every subgradient `g` of `|·|`
  at any point satisfies `|g| ≤ 1`.
* `Convex.isL1Subgradient_componentwise`: a componentwise
  characterization of `ℓ¹` subgradients via `IsAbsSubgradient` per
  coordinate.

## Implementation notes

`IsAbsSubgradient` is *not* a typeclass-style predicate: whether `g`
witnesses the subgradient inequality depends on the *value* of `g`, so
making it an `instance` would not be useful (Lean cannot synthesize a
witness without the value). For the same reason `IsL1Subgradient` is a
plain definition.

## References

* Stephen Boyd and Lieven Vandenberghe, *Convex Optimization*,
  Cambridge University Press, 2004, §3.1.5 and §A.5.
* Jean-Baptiste Hiriart-Urruty and Claude Lemaréchal,
  *Convex Analysis and Minimization Algorithms I*, Springer, 1993,
  Chapter VI.
* Francis Bach, *Learning Theory from First Principles*, MIT Press,
  2024, §8.2 (Lasso optimality).

## Tags

subgradient, subdifferential, convex, lasso, absolute value, l1 norm
-/

namespace Convex

@[expose] public section

/-- A real number `g` is a *subgradient* of `|·| : ℝ → ℝ` at `x` if
the subgradient inequality `|y| ≥ |x| + g * (y - x)` holds for every
`y : ℝ`. -/
def IsAbsSubgradient (x g : ℝ) : Prop :=
  ∀ y : ℝ, |y| ≥ |x| + g * (y - x)

/-- At any strictly positive point, the constant `1` is a subgradient of
the absolute-value function. -/
theorem isAbsSubgradient_of_pos {x : ℝ} (hx : 0 < x) : IsAbsSubgradient x 1 := by
  intro y
  have hx_abs : |x| = x := abs_of_pos hx
  have hy_abs : |y| ≥ y := le_abs_self y
  rw [hx_abs, one_mul]
  linarith [hy_abs]

/-- At any strictly negative point, the constant `-1` is a subgradient
of the absolute-value function. -/
theorem isAbsSubgradient_of_neg {x : ℝ} (hx : x < 0) : IsAbsSubgradient x (-1) := by
  intro y
  have hx_abs : |x| = -x := abs_of_neg hx
  have hy_abs : |y| ≥ -y := neg_le_abs y
  rw [hx_abs]
  linarith [hy_abs]

/-- The subdifferential of `|·|` at `0` is exactly the closed interval
`[-1, 1]`: a real `g` is a subgradient at `0` if and only if
`|g| ≤ 1`. -/
theorem isAbsSubgradient_zero_iff {g : ℝ} : IsAbsSubgradient 0 g ↔ |g| ≤ 1 := by
  constructor
  · intro h
    -- Probe the subgradient inequality at `y = 1` and `y = -1`.
    have h1 : |(1 : ℝ)| ≥ |(0 : ℝ)| + g * (1 - 0) := h 1
    have h2 : |(-1 : ℝ)| ≥ |(0 : ℝ)| + g * (-1 - 0) := h (-1)
    rw [abs_zero, abs_one] at h1
    rw [abs_zero, abs_neg, abs_one] at h2
    have hg_le : g ≤ 1 := by linarith
    have hg_ge : -1 ≤ g := by linarith
    exact abs_le.mpr ⟨hg_ge, hg_le⟩
  · intro h y
    rw [abs_zero, zero_add]
    rcases abs_le.mp h with ⟨hg_lb, hg_ub⟩
    rcases le_or_gt 0 y with hy | hy
    · have hy_abs : |y| = y := abs_of_nonneg hy
      rw [hy_abs]
      nlinarith
    · have hy_abs : |y| = -y := abs_of_neg hy
      rw [hy_abs]
      nlinarith

/-- At every nonzero point, `Real.sign x` is a subgradient of `|·|` at
`x`. (It is the unique one, by `isAbsSubgradient_zero_iff` paired with
`abs_subgradient_mem_interval`.) -/
theorem isAbsSubgradient_sign {x : ℝ} (hx : x ≠ 0) :
    IsAbsSubgradient x (Real.sign x) := by
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · rw [Real.sign_of_neg hx_neg]
    exact isAbsSubgradient_of_neg hx_neg
  · rw [Real.sign_of_pos hx_pos]
    exact isAbsSubgradient_of_pos hx_pos

/-- Every subgradient `g` of `|·|` at any point `x` satisfies
`|g| ≤ 1`. This is the standard a-priori bound on the subdifferential
of a `1`-Lipschitz convex function. -/
theorem abs_subgradient_mem_interval {x g : ℝ} (h : IsAbsSubgradient x g) :
    |g| ≤ 1 := by
  -- Probe the subgradient inequality at `y = x + 1` and `y = x - 1`.
  have h1 : |x + 1| ≥ |x| + g * ((x + 1) - x) := h (x + 1)
  have h2 : |x - 1| ≥ |x| + g * ((x - 1) - x) := h (x - 1)
  have h1' : |x + 1| ≥ |x| + g := by simpa using h1
  have h2' : |x - 1| ≥ |x| - g := by
    have := h2
    simp only [sub_sub_cancel_left] at this
    linarith
  -- Combine with the triangle-inequality bounds `|x ± 1| ≤ |x| + 1`.
  have hub1 : |x + 1| ≤ |x| + 1 := by
    have := abs_add_le x 1
    simpa using this
  have hub2 : |x - 1| ≤ |x| + 1 := by
    have := abs_sub x 1
    simpa using this
  have hg_le : g ≤ 1 := by linarith
  have hg_ge : -1 ≤ g := by linarith
  exact abs_le.mpr ⟨hg_ge, hg_le⟩

/-- A function `g : Fin n → ℝ` is an *`ℓ¹` subgradient* of
`v : Fin n → ℝ` if every component `g i` is a scalar subgradient of
`|·|` at `v i`. -/
def IsL1Subgradient {n : ℕ} (v g : Fin n → ℝ) : Prop :=
  ∀ i : Fin n, IsAbsSubgradient (v i) (g i)

/-- Componentwise characterization of `ℓ¹` subgradients: a vector `g` is
an `ℓ¹` subgradient of `v` if and only if, for every coordinate `i`,
either `v i ≠ 0` and `g i = Real.sign (v i)`, or `v i = 0` and
`|g i| ≤ 1`. -/
theorem isL1Subgradient_componentwise {n : ℕ} {v g : Fin n → ℝ} :
    IsL1Subgradient v g ↔
      ∀ i : Fin n,
        (v i ≠ 0 ∧ g i = Real.sign (v i)) ∨ (v i = 0 ∧ |g i| ≤ 1) := by
  constructor
  · intro h i
    by_cases hvi : v i = 0
    · refine Or.inr ⟨hvi, ?_⟩
      have hgi : IsAbsSubgradient 0 (g i) := hvi ▸ h i
      exact (isAbsSubgradient_zero_iff).mp hgi
    · refine Or.inl ⟨hvi, ?_⟩
      have hgi : IsAbsSubgradient (v i) (g i) := h i
      have habs : |g i| ≤ 1 := abs_subgradient_mem_interval hgi
      rcases lt_or_gt_of_ne hvi with hneg | hpos
      · -- `v i < 0`: the subgradient inequality at `y = 0` forces `g i = -1`.
        rw [Real.sign_of_neg hneg]
        have h0 : |(0 : ℝ)| ≥ |v i| + g i * (0 - v i) := hgi 0
        rw [abs_zero, abs_of_neg hneg] at h0
        have hge : -1 ≤ g i := (abs_le.mp habs).1
        have hle : g i ≤ -1 := by nlinarith
        linarith
      · -- `v i > 0`: the subgradient inequality at `y = 0` forces `g i = 1`.
        rw [Real.sign_of_pos hpos]
        have h0 : |(0 : ℝ)| ≥ |v i| + g i * (0 - v i) := hgi 0
        rw [abs_zero, abs_of_pos hpos] at h0
        have hle : g i ≤ 1 := (abs_le.mp habs).2
        have hge : 1 ≤ g i := by nlinarith
        linarith
  · intro h i
    rcases h i with ⟨hvi, hgi⟩ | ⟨hvi, hgi⟩
    · rw [hgi]
      exact isAbsSubgradient_sign hvi
    · rw [hvi]
      exact (isAbsSubgradient_zero_iff).mpr hgi

/-! ### Examples

The following examples demonstrate the three regimes of the scalar
subdifferential of `|·|`. -/

/-- At any strictly positive point, the value `1` witnesses the
subgradient inequality. -/
example : IsAbsSubgradient (2 : ℝ) 1 := isAbsSubgradient_of_pos (by norm_num)

/-- At `0`, every value in `[-1, 1]` is a subgradient — for instance
`1/2`. -/
example : IsAbsSubgradient (0 : ℝ) (1 / 2) :=
  isAbsSubgradient_zero_iff.mpr (by rw [abs_of_pos] <;> norm_num)

/-- At any nonzero point, `Real.sign x` is a subgradient. -/
example : IsAbsSubgradient (-3 : ℝ) (Real.sign (-3)) :=
  isAbsSubgradient_sign (by norm_num)

end

end Convex

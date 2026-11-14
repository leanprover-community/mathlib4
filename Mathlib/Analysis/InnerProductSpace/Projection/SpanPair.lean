/-
Copyright (c) 2026 Daniel Toupin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Toupin
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic

import Mathlib.Tactic.Ring

/-!
# Explicit projection onto the span of two vectors

This file evaluates the orthogonal projection onto the span of two vectors in a real
inner product space using Cramer's rule for the two-by-two Gram matrix, and evaluates
the squared distance to that span using the inverse Gram matrix.

## Main results

* `InnerProductSpace.starProjection_span_pair`: the orthogonal projection of `x` onto
  `span ℝ {u, v}` as an explicit linear combination of `u` and `v`.
* `InnerProductSpace.norm_sub_starProjection_span_pair_sq`: the squared norm of
  `x - (span ℝ {u, v}).starProjection x` in terms of the Gram matrix of `u` and `v` and
  the inner products of `x` with `u` and `v`.

The projection itself is Mathlib's `Submodule.starProjection`; no new projection
operator is introduced. The ambient space need not be complete or finite-dimensional:
the pair span is finite-dimensional, and the `HasOrthogonalProjection` instance for it
can be supplied from `FiniteDimensional.span_of_finite` together with
`FiniteDimensional.completeSpace`. The only hypothesis on the pair is that the Gram
determinant is nonzero, that is, that `u` and `v` are linearly independent.
-/

public section

open scoped InnerProductSpace
open Submodule

namespace InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cramer's-rule evaluation of the orthogonal projection onto a two-vector span:
the coefficients of the projection of `x` onto `span ℝ {u, v}` are obtained by applying
the inverse of the Gram matrix of `u` and `v` to `(⟪u, x⟫, ⟪v, x⟫)`. -/
theorem starProjection_span_pair (u v x : E)
    [(span ℝ ({u, v} : Set E)).HasOrthogonalProjection]
    (hdet : ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2 ≠ 0) :
    (span ℝ ({u, v} : Set E)).starProjection x =
      ((⟪v, v⟫_ℝ * ⟪u, x⟫_ℝ - ⟪u, v⟫_ℝ * ⟪v, x⟫_ℝ) /
        (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2)) • u +
      ((⟪u, u⟫_ℝ * ⟪v, x⟫_ℝ - ⟪u, v⟫_ℝ * ⟪u, x⟫_ℝ) /
        (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2)) • v := by
  let a := (⟪v, v⟫_ℝ * ⟪u, x⟫_ℝ - ⟪u, v⟫_ℝ * ⟪v, x⟫_ℝ) /
    (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2)
  let b := (⟪u, u⟫_ℝ * ⟪v, x⟫_ℝ - ⟪u, v⟫_ℝ * ⟪u, x⟫_ℝ) /
    (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2)
  change (span ℝ ({u, v} : Set E)).starProjection x = a • u + b • v
  have ha : a * ⟪u, u⟫_ℝ + b * ⟪u, v⟫_ℝ = ⟪u, x⟫_ℝ := by
    dsimp [a, b]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (div_eq_iff hdet).mpr
    ring
  have hb : a * ⟪u, v⟫_ℝ + b * ⟪v, v⟫_ℝ = ⟪v, x⟫_ℝ := by
    dsimp [a, b]
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    apply (div_eq_iff hdet).mpr
    ring
  have hu : ⟪x - (a • u + b • v), u⟫_ℝ = 0 := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_comm u x, real_inner_comm u v, ha, sub_self]
  have hv : ⟪x - (a • u + b • v), v⟫_ℝ = 0 := by
    simp only [inner_sub_left, inner_add_left, real_inner_smul_left,
      real_inner_comm v x, hb, sub_self]
  refine (span ℝ ({u, v} : Set E)).eq_starProjection_of_mem_of_inner_eq_zero
    (mem_span_pair.mpr ⟨a, b, rfl⟩) ?_
  intro w hw
  obtain ⟨c, d, rfl⟩ := mem_span_pair.mp hw
  simp only [inner_add_right, real_inner_smul_right, hu, hv, mul_zero, add_zero]

/-- Squared distance to a two-vector span, evaluated using the inverse Gram matrix:
the squared norm of the residual `x - (span ℝ {u, v}).starProjection x` is `‖x‖ ^ 2`
minus the quadratic form of the inverse Gram matrix of `u` and `v` evaluated at
`(⟪u, x⟫, ⟪v, x⟫)`. -/
theorem norm_sub_starProjection_span_pair_sq (u v x : E)
    [(span ℝ ({u, v} : Set E)).HasOrthogonalProjection]
    (hdet : ⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2 ≠ 0) :
    ‖x - (span ℝ ({u, v} : Set E)).starProjection x‖ ^ 2 =
      ‖x‖ ^ 2 - (⟪v, v⟫_ℝ * ⟪u, x⟫_ℝ ^ 2 -
        2 * ⟪u, v⟫_ℝ * ⟪u, x⟫_ℝ * ⟪v, x⟫_ℝ +
        ⟪u, u⟫_ℝ * ⟪v, x⟫_ℝ ^ 2) /
        (⟪u, u⟫_ℝ * ⟪v, v⟫_ℝ - ⟪u, v⟫_ℝ ^ 2) := by
  let K := span ℝ ({u, v} : Set E)
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection x K
  rw [K.starProjection_orthogonal_val] at hpy
  have hip : ⟪K.starProjection x, x⟫_ℝ = ‖K.starProjection x‖ ^ 2 :=
    K.re_inner_starProjection_eq_normSq x
  calc
    _ = ‖x‖ ^ 2 - ⟪K.starProjection x, x⟫_ℝ := by
      apply (eq_sub_iff_add_eq).mpr
      rw [hip]
      exact (add_comm _ _).trans hpy.symm
    _ = _ := by
      dsimp only [K]
      rw [starProjection_span_pair u v x hdet]
      simp only [inner_add_left, real_inner_smul_left]
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
      congr 2
      ring

end InnerProductSpace

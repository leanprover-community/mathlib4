/-
Copyright (c) 2026 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions

/-!
# Hecke operators on functions on the upper half-plane

This file defines the Hecke operators `T n` acting on functions `f : ℍ → ℂ`, for a
positive integer `n`, as a weighted sum of weight-`k` slash actions over a set of coset
representatives of `SL(2, ℤ) ∖ Δ n`, where `Δ n` is the set of integer matrices of determinant `n`.

The standard choice of representatives is the set of upper-triangular matrices
`!![a, b; 0, d]` with `a * d = n`, `a, d > 0` and `0 ≤ b < d`. Concretely, on a weight-`k` form this
gives the classical formula
`(T n f) z = n ^ (k - 1) * ∑_{a * d = n} ∑_{0 ≤ b < d} d ^ (-k) * f ((a * z + b) / d)`.

## Main definitions

* `ModularForm.heckeMatrix a b d`: the representative matrix `!![a, b; 0, d]` as an element of
  `GL (Fin 2) ℝ` (defaulting to `1` when `a * d = 0`).
* `ModularForm.heckeOp n k`: the weight-`k` Hecke operator `T n` as a `ℂ`-linear endomorphism of
  `ℍ → ℂ`.

## Implementation notes

`heckeMatrix` returns `1` if the determinant `a * d` vanishes.

## TODO

* Show that `heckeOp` preserves `ModularForm` and `CuspForm`.
* Compute the effect of `heckeOp` on `q`-expansions.
* Prove multiplicativity of the `T n` (for the Hecke algebra).
-/

@[expose] public section

open Complex UpperHalfPlane

open scoped ModularForm MatrixGroups

namespace ModularForm

variable (k : ℤ)

/-- The representative matrix `!![a, b; 0, d]` (of determinant `a * d`) as an element of
`GL (Fin 2) ℝ`. When `a * d = 0` we return the identity matrix instead. -/
noncomputable def heckeMatrix (a b d : ℕ) : GL (Fin 2) ℝ :=
  if h : ((a : ℝ) * d) ≠ 0 then
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![(a : ℝ), (b : ℝ); 0, (d : ℝ)]
      (by rw [Matrix.det_fin_two_of]; simpa using h)
  else 1

/-- The determinant of `heckeMatrix a b d` is positive. -/
lemma heckeMatrix_det_pos (a b d : ℕ) : 0 < (heckeMatrix a b d).det.val := by
  rw [heckeMatrix]
  split_ifs with h
  · rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_mkOfDetNeZero,
      Matrix.det_fin_two_of]
    have : (0 : ℝ) ≤ (a : ℝ) * d := by positivity
    simp only [mul_zero, sub_zero]
    exact lt_of_le_of_ne this (Ne.symm (by simpa using h))
  · simp

/-- `σ` is the identity on `heckeMatrix a b d`, since the determinant is positive. -/
@[simp]
lemma σ_heckeMatrix (a b d : ℕ) (z : ℂ) : σ (heckeMatrix a b d) z = z := by
  rw [σ, if_pos (heckeMatrix_det_pos a b d)]
  rfl

/-- The weight-`k` Hecke operator `T n` acting on functions `f : ℍ → ℂ`, as a `ℂ`-linear map.

It is the sum of the weight-`k` slash actions over the upper-triangular representatives
`!![a, b; 0, d]` with `a * d = n` and `0 ≤ b < d`. -/
noncomputable def heckeOp (n : ℕ) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ∑ a ∈ n.divisors, ∑ b ∈ Finset.range (n / a), f ∣[k] heckeMatrix a b (n / a)
  map_add' f g := by
    simp only [SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [smul_slash, σ_heckeMatrix]

lemma heckeOp_apply (n : ℕ) (f : ℍ → ℂ) :
    heckeOp k n f = ∑ a ∈ n.divisors, ∑ b ∈ Finset.range (n / a), f ∣[k] heckeMatrix a b (n / a) :=
  rfl

end ModularForm

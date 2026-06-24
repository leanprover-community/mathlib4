/-
Copyright (c) 2026 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Mathlib.NumberTheory.ModularForms.SlashActions
public import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices

/-!
# Hecke operators on functions on the upper half-plane

This file defines the Hecke operators `T n` acting on functions `f : ℍ → ℂ`, for a
positive integer `n`, as a weighted sum of weight-`k` slash actions over the set of canonical
representatives `FixedDetMatrices.reps n` of the orbits of `SL(2, ℤ)` acting on the integer
matrices `Δ n` of determinant `n`.

For `n > 0` the set `reps n` is the set of upper-triangular matrices `!![a, b; 0, d]` with
`a * d = n`, `a, d > 0` and `0 ≤ b < d`. On a weight-`k` form this gives the classical formula
`(T n f) z = n ^ (k - 1) * ∑_{a * d = n} ∑_{0 ≤ b < d} d ^ (-k) * f ((a * z + b) / d)`.

## Main definitions

* `ModularForm.heckeOp n k`: the weight-`k` Hecke operator `T n` as a `ℂ`-linear endomorphism of
  `ℍ → ℂ`.

## TODO

* Show that `heckeOp` preserves `ModularForm` and `CuspForm`, via the fact that right multiplication
  by `SL(2, ℤ)` permutes the representatives `reps n`.
* Compute the effect of `heckeOp` on `q`-expansions.
* Prove multiplicativity of the `T n`.
-/

@[expose] public section

open Complex UpperHalfPlane

open scoped ModularForm MatrixGroups


namespace FixedDetMatrices

/-- The element of `GL (Fin 2) ℝ` obtained from a representative `A ∈ reps n` by mapping its integer
entries to `ℝ`; the determinant `n` is then a positive (in particular nonzero) real number. -/
noncomputable def reps_toGL {n : ℕ+} (A : reps (n : ℤ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (A.1.1.map (Int.castRingHom ℝ)) <| by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, A.1.2, eq_intCast]
    simp


end FixedDetMatrices

namespace ModularForm

open FixedDetMatrices

variable (k : ℤ)


/-- The weight-`k` Hecke operator `T n` acting on functions `f : ℍ → ℂ`, as a `ℂ`-linear map.

It is the sum of the weight-`k` slash actions over the canonical representatives `reps n` of the
orbits of `SL(2, ℤ)` on integer matrices of determinant `n`. -/
noncomputable def heckeOp (n : ℕ+) : (ℍ → ℂ) →ₗ[ℂ] (ℍ → ℂ) where
  toFun f := ∑ A : reps (n : ℤ), f ∣[k] reps_toGL A
  map_add' f g := by
    simp only [SlashAction.add_slash, Finset.sum_add_distrib]
  map_smul' c f := by
    simp only [RingHom.id_apply, Finset.smul_sum]
    exact Finset.sum_congr rfl fun A _ => by sorry

lemma heckeOp_apply (n : ℕ+) (f : ℍ → ℂ) :
    heckeOp k n f = ∑ A : reps (n : ℤ), f ∣[k] reps_toGL A :=
  rfl

end ModularForm

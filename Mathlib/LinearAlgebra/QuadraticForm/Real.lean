/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Data.Sign
import Mathlib.Algebra.CharP.Invertible
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Complex.Abs

#align_import linear_algebra.quadratic_form.real from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Real quadratic forms

Sylvester's law of inertia `equivalent_one_neg_one_weighted_sum_squared`:
A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0.

When the real quadratic form is nondegenerate we can take the weights to be ±1,
as in `equivalent_one_zero_neg_one_weighted_sum_squared`.

-/


namespace QuadraticForm

open Finset SignType

variable {ι : Type*} [Fintype ι]

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometryEquivSignWeightedSumSquares (w : ι → ℝ) :
    IsometryEquiv (weightedSumSquares ℝ w)
      (weightedSumSquares ℝ (fun i ↦ (sign (w i) : ℝ))) := by
  let u i := if h : w i = 0 then (1 : ℝˣ) else Units.mk0 (w i) h
  have hu : ∀ i : ι, 1 / √|(u i : ℝ)| ≠ 0 := fun i ↦
    have : (u i : ℝ) ≠ 0 := (u i).ne_zero
    by positivity
  have hwu : ∀ i, w i / |(u i : ℝ)| = sign (w i) := fun i ↦ by
    by_cases hi : w i = 0 <;> field_simp [hi, u]
  convert (weightedSumSquares ℝ w).isometryEquivBasisRepr
    ((Pi.basisFun ℝ ι).unitsSMul fun i => .mk0 _ (hu i))
  ext1 v
  classical
  suffices ∑ i, (w i / |(u i : ℝ)|) * v i ^ 2 = ∑ i, w i * (v i ^ 2 * |(u i : ℝ)|⁻¹) by
    simpa [basisRepr_apply, Basis.unitsSMul_apply, ← _root_.sq, mul_pow, ← hwu]
  exact sum_congr rfl fun j _ ↦ by ring
#align quadratic_form.isometry_sign_weighted_sum_squares QuadraticForm.isometryEquivSignWeightedSumSquares

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1, `SignType` version. -/
theorem equivalent_sign_ne_zero_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : (associated (R := ℝ) Q).SeparatingLeft) :
    ∃ w : Fin (FiniteDimensional.finrank ℝ M) → SignType,
      (∀ i, w i ≠ 0) ∧ Equivalent Q (weightedSumSquares ℝ fun i ↦ (w i : ℝ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨sign ∘ ((↑) : ℝˣ → ℝ) ∘ w, fun i => sign_ne_zero.2 (w i).ne_zero,
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares (((↑) : ℝˣ → ℝ) ∘ w))⟩⟩

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : (associated (R := ℝ) Q).SeparatingLeft) :
    ∃ w : Fin (FiniteDimensional.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, hw₀, hw⟩ := Q.equivalent_sign_ne_zero_weighted_sum_squared hQ
  ⟨(w ·), fun i ↦ by cases hi : w i <;> simp_all, hw⟩
#align quadratic_form.equivalent_one_neg_one_weighted_sum_squared QuadraticForm.equivalent_one_neg_one_weighted_sum_squared

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0, `SignType` version. -/
theorem equivalent_signType_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (FiniteDimensional.finrank ℝ M) → SignType,
      Equivalent Q (weightedSumSquares ℝ fun i ↦ (w i : ℝ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares
  ⟨sign ∘ w, ⟨hw₁.trans (isometryEquivSignWeightedSumSquares w)⟩⟩

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (FiniteDimensional.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, hw⟩ := Q.equivalent_signType_weighted_sum_squared
  ⟨(w ·), fun i ↦ by cases h : w i <;> simp [h], hw⟩
#align quadratic_form.equivalent_one_zero_neg_one_weighted_sum_squared QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared

end QuadraticForm

/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sign

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

open scoped BigOperators

open Real Finset

variable {ι : Type*} [Fintype ι]

/-- The isometry between a weighted sum of squares with weights `u` on the
(non-zero) real numbers and the weighted sum of squares with weights `sign ∘ u`. -/
noncomputable def isometryEquivSignWeightedSumSquares [DecidableEq ι] (w : ι → ℝ) :
    IsometryEquiv (weightedSumSquares ℝ w) (weightedSumSquares ℝ (Real.sign ∘ w)) := by
  let u i := if h : w i = 0 then (1 : ℝˣ) else Units.mk0 (w i) h
  have hu' : ∀ i : ι, (Real.sign (u i) * u i) ^ (-(1 / 2 : ℝ)) ≠ 0 := by
    intro i
    refine' (ne_of_lt (Real.rpow_pos_of_pos (sign_mul_pos_of_ne_zero _ <| Units.ne_zero _) _)).symm
  convert
    (weightedSumSquares ℝ w).isometryEquivBasisRepr
      ((Pi.basisFun ℝ ι).unitsSMul fun i => (isUnit_iff_ne_zero.2 <| hu' i).unit)
  ext1 v
  rw [basisRepr_apply, weightedSumSquares_apply, weightedSumSquares_apply]
  refine' sum_congr rfl fun j hj => _
  have hsum :
    (∑ i : ι, v i • ((isUnit_iff_ne_zero.2 <| hu' i).unit : ℝ) • (Pi.basisFun ℝ ι) i) j =
      v j • (Real.sign (u j) * u j) ^ (-(1 / 2 : ℝ)) := by
    rw [Finset.sum_apply, sum_eq_single j, Pi.basisFun_apply, IsUnit.unit_spec,
      LinearMap.stdBasis_apply, Pi.smul_apply, Pi.smul_apply, Function.update_same, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_one]
    intro i _ hij
    rw [Pi.basisFun_apply, LinearMap.stdBasis_apply, Pi.smul_apply, Pi.smul_apply,
      Function.update_noteq hij.symm, Pi.zero_apply, smul_eq_mul, smul_eq_mul,
      mul_zero, mul_zero]
    intro hj'; exact False.elim (hj' hj)
  simp_rw [Basis.unitsSMul_apply]
  erw [hsum]
  simp only [Function.comp, smul_eq_mul]
  split_ifs with h
  · simp only [h, zero_smul, zero_mul, Real.sign_zero]
  have hwu : w j = u j := by simp only [dif_neg h, Units.val_mk0]
  simp only [Units.val_mk0]
  rw [hwu]
  suffices
    (u j : ℝ).sign * v j * v j =
      (Real.sign (u j) * u j) ^ (-(1 / 2 : ℝ)) * (Real.sign (u j) * u j) ^ (-(1 / 2 : ℝ)) *
            u j *
          v j *
        v j
    by erw [← mul_assoc, this]; ring
  rw [← Real.rpow_add (sign_mul_pos_of_ne_zero _ <| Units.ne_zero _),
    show -(1 / 2 : ℝ) + -(1 / 2) = -1 by ring, Real.rpow_neg_one, mul_inv, inv_sign,
    mul_assoc (Real.sign (u j)) (u j)⁻¹, inv_mul_cancel (Units.ne_zero _), mul_one]
#align quadratic_form.isometry_sign_weighted_sum_squares QuadraticForm.isometryEquivSignWeightedSumSquares

/-- **Sylvester's law of inertia**: A nondegenerate real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1. -/
theorem equivalent_one_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) (hQ : (associated (R := ℝ) Q).Nondegenerate) :
    ∃ w : Fin (FiniteDimensional.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨Real.sign ∘ ((↑) : ℝˣ → ℝ) ∘ w, fun i => sign_apply_eq_of_ne_zero (w i) (w i).ne_zero,
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares (((↑) : ℝˣ → ℝ) ∘ w))⟩⟩
#align quadratic_form.equivalent_one_neg_one_weighted_sum_squared QuadraticForm.equivalent_one_neg_one_weighted_sum_squared

/-- **Sylvester's law of inertia**: A real quadratic form is equivalent to a weighted
sum of squares with the weights being ±1 or 0. -/
theorem equivalent_one_zero_neg_one_weighted_sum_squared {M : Type*} [AddCommGroup M] [Module ℝ M]
    [FiniteDimensional ℝ M] (Q : QuadraticForm ℝ M) :
    ∃ w : Fin (FiniteDimensional.finrank ℝ M) → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧ Equivalent Q (weightedSumSquares ℝ w) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares
  ⟨Real.sign ∘ ((↑) : ℝ → ℝ) ∘ w, fun i => sign_apply_eq (w i),
    ⟨hw₁.trans (isometryEquivSignWeightedSumSquares w)⟩⟩
#align quadratic_form.equivalent_one_zero_neg_one_weighted_sum_squared QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared

end QuadraticForm

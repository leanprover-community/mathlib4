/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

#align_import linear_algebra.quadratic_form.complex from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Quadratic forms over the complex numbers

`equivalent_sum_squares`: A nondegenerate quadratic form over the complex numbers is equivalent to
a sum of squares.

-/


namespace QuadraticForm

open scoped BigOperators

open Finset

variable {ι : Type*} [Fintype ι]

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weightedSumSquares` with weights 1 or 0. -/
noncomputable def isometryEquivSumSquares [DecidableEq ι] (w' : ι → ℂ) :
    IsometryEquiv (weightedSumSquares ℂ w')
      (weightedSumSquares ℂ (fun i => if w' i = 0 then 0 else 1 : ι → ℂ)) := by
  let w i := if h : w' i = 0 then (1 : Units ℂ) else Units.mk0 (w' i) h
  -- ⊢ IsometryEquiv (weightedSumSquares ℂ w') (weightedSumSquares ℂ fun i => if w' …
  have hw' : ∀ i : ι, (w i : ℂ) ^ (-(1 / 2 : ℂ)) ≠ 0 := by
    intro i hi
    exact (w i).ne_zero ((Complex.cpow_eq_zero_iff _ _).1 hi).1
  convert (weightedSumSquares ℂ w').isometryEquivBasisRepr
    ((Pi.basisFun ℂ ι).unitsSMul fun i => (isUnit_iff_ne_zero.2 <| hw' i).unit)
  ext1 v
  -- ⊢ ↑(weightedSumSquares ℂ fun i => if w' i = 0 then 0 else 1) v = ↑(basisRepr ( …
  erw [basisRepr_apply, weightedSumSquares_apply, weightedSumSquares_apply]
  -- ⊢ ∑ i : ι, (if w' i = 0 then 0 else 1) • (v i * v i) = ∑ i : ι, w' i • (Finset …
  refine' sum_congr rfl fun j hj => _
  -- ⊢ (if w' j = 0 then 0 else 1) • (v j * v j) = w' j • (Finset.sum univ (fun i = …
  have hsum : (∑ i : ι, v i • ((isUnit_iff_ne_zero.2 <| hw' i).unit : ℂ) • (Pi.basisFun ℂ ι) i) j =
      v j • w j ^ (-(1 / 2 : ℂ)) := by
    rw [Finset.sum_apply, sum_eq_single j, Pi.basisFun_apply, IsUnit.unit_spec,
      LinearMap.stdBasis_apply, Pi.smul_apply, Pi.smul_apply, Function.update_same, smul_eq_mul,
      smul_eq_mul, smul_eq_mul, mul_one]
    intro i _ hij
    rw [Pi.basisFun_apply, LinearMap.stdBasis_apply, Pi.smul_apply, Pi.smul_apply,
      Function.update_noteq hij.symm, Pi.zero_apply, smul_eq_mul, smul_eq_mul,
      mul_zero, mul_zero]
    intro hj'; exact False.elim (hj' hj)
  simp_rw [Basis.unitsSMul_apply]
  -- ⊢ (if w' j = 0 then 0 else 1) • (v j * v j) = w' j • (Finset.sum univ (fun x = …
  erw [hsum, smul_eq_mul]
  -- ⊢ (if w' j = 0 then 0 else 1) * (v j * v j) = w' j • (v j • ↑(w j) ^ (-(1 / 2) …
  split_ifs with h
  -- ⊢ 0 * (v j * v j) = w' j • (v j • ↑1 ^ (-(1 / 2)) * v j • ↑1 ^ (-(1 / 2)))
  · simp only [h, zero_smul, zero_mul]
    -- 🎉 no goals
  have hww' : w' j = w j := by simp only [dif_neg h, Units.val_mk0]
  -- ⊢ 1 * (v j * v j) = w' j • (v j • ↑(Units.mk0 (w' j) h) ^ (-(1 / 2)) * v j • ↑ …
  simp only [one_mul, Units.val_mk0, smul_eq_mul]
  -- ⊢ v j * v j = w' j * (v j * w' j ^ (-(1 / 2)) * (v j * w' j ^ (-(1 / 2))))
  rw [hww']
  -- ⊢ v j * v j = ↑(w j) * (v j * ↑(w j) ^ (-(1 / 2)) * (v j * ↑(w j) ^ (-(1 / 2))))
  suffices v j * v j = w j ^ (-(1 / 2 : ℂ)) * w j ^ (-(1 / 2 : ℂ)) * w j * v j * v j by
    rw [this]; ring
  rw [← Complex.cpow_add _ _ (w j).ne_zero, show -(1 / 2 : ℂ) + -(1 / 2) = -1 by simp [← two_mul],
    Complex.cpow_neg_one, inv_mul_cancel (w j).ne_zero, one_mul]
#align quadratic_form.isometry_sum_squares QuadraticForm.isometryEquivSumSquares

/-- The isometry between a weighted sum of squares on the complex numbers and the
sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`. -/
noncomputable def isometryEquivSumSquaresUnits [DecidableEq ι] (w : ι → Units ℂ) :
    IsometryEquiv (weightedSumSquares ℂ w) (weightedSumSquares ℂ (1 : ι → ℂ)) := by
  simpa using isometryEquivSumSquares ((↑) ∘ w)
  -- 🎉 no goals
#align quadratic_form.isometry_sum_squares_units QuadraticForm.isometryEquivSumSquaresUnits

/-- A nondegenerate quadratic form on the complex numbers is equivalent to
the sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`. -/
theorem equivalent_sum_squares {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q : QuadraticForm ℂ M) (hQ : (associated (R₁ := ℂ) Q).Nondegenerate) :
    Equivalent Q (weightedSumSquares ℂ (1 : Fin (FiniteDimensional.finrank ℂ M) → ℂ)) :=
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometryEquivSumSquaresUnits w)⟩
#align quadratic_form.equivalent_sum_squares QuadraticForm.equivalent_sum_squares

/-- All nondegenerate quadratic forms on the complex numbers are equivalent. -/
theorem complex_equivalent {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (Q₁ Q₂ : QuadraticForm ℂ M) (hQ₁ : (associated (R₁ := ℂ) Q₁).Nondegenerate)
    (hQ₂ : (associated (R₁ := ℂ) Q₂).Nondegenerate) : Equivalent Q₁ Q₂ :=
  (Q₁.equivalent_sum_squares hQ₁).trans (Q₂.equivalent_sum_squares hQ₂).symm
#align quadratic_form.complex_equivalent QuadraticForm.complex_equivalent

end QuadraticForm

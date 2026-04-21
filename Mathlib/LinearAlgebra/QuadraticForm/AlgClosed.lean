/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Quadratic forms over an algebraically closed field

`equivalent_sum_squares`: A nondegenerate quadratic form over an algebraically closed field of
characteristic not equal to 2 is equivalent to a sum of squares.

TODO: generalize `QuadraticForm.isometryEquivSumSquares` to quadratically closed field.
-/

public section

namespace QuadraticForm

open Finset QuadraticMap

variable {ι : Type*} [Fintype ι] {K : Type*} [Field K] [IsAlgClosed K]

/-- The isometry between a weighted sum of squares on an algebraically closed field and the
sum of squares, i.e. `weightedSumSquares` with weights 1 or 0. -/
noncomputable def isometryEquivSumSquares [DecidableEq K] (w : ι → K) :
    IsometryEquiv (weightedSumSquares K w)
      (weightedSumSquares K (fun i => if w i = 0 then 0 else 1 : ι → K)) := by
  refine isometryEquivWeightedSumSquaresWeightedSumSquares (fun i => if h : w i = 0 then 1 else
    Units.mk0 (IsAlgClosed.exists_eq_mul_self (w i)).choose (by
      rw [← mul_self_eq_zero.ne, ← (IsAlgClosed.exists_eq_mul_self (w i)).choose_spec]
      simpa using h)) ?_
  intro i
  split_ifs with h <;>
    simp [h, pow_two, ← (IsAlgClosed.exists_eq_mul_self (w i : K)).choose_spec]

/-- The isometry between a weighted sum of squares on an algebraically closed field and the
sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`. -/
noncomputable def isometryEquivSumSquaresUnits [DecidableEq K] (w : ι → Kˣ) :
    IsometryEquiv (weightedSumSquares K w) (weightedSumSquares K (1 : ι → K)) :=
  (isometryEquivSumSquares (fun i ↦ (w i).val)).trans (weightedSumSquaresCongr (by ext; simp))

/-- A nondegenerate quadratic form on an algebraically closed field of characteristic not equal to 2
is equivalent to the sum of squares, i.e. `weightedSumSquares` with weight `fun (i : ι) => 1`. -/
theorem equivalent_weightedSumSquares_of_isAlgClosed [Invertible (2 : K)] {M : Type*}
    [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q : QuadraticForm K M) (hQ : (associated Q).SeparatingLeft) :
    Equivalent Q (weightedSumSquares K (1 : Fin (Module.finrank K M) → K)) :=
  open Classical in
  let ⟨w, ⟨hw₁⟩⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  ⟨hw₁.trans (isometryEquivSumSquaresUnits w)⟩

/-- All nondegenerate quadratic forms on an algebraically closed field of characteristic not equal
to 2 are equivalent. -/
theorem equivalent_of_isAlgClosed [Invertible (2 : K)] {M : Type*} [AddCommGroup M] [Module K M]
    [FiniteDimensional K M] (Q₁ Q₂ : QuadraticForm K M)
    (hQ₁ : (associated Q₁).SeparatingLeft)
    (hQ₂ : (associated Q₂).SeparatingLeft) : Equivalent Q₁ Q₂ :=
  open Classical in
  (Q₁.equivalent_weightedSumSquares_of_isAlgClosed hQ₁).trans
  (Q₂.equivalent_weightedSumSquares_of_isAlgClosed hQ₂).symm

end QuadraticForm

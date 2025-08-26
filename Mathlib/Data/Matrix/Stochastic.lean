/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Stochastic matrices

This file gives the key definitions and results about matrices that are
(possibly) only singly stochastic (both row and column).

## Main definitions

* `rowStochastic`
* `colStochastic`

## Main statements

* `pdist_vecMul_of_mem_rowStochastic` if a row stochastic matrix is applied to
  a positive vector with unit `ℓ₁`-norm (informally, a probility distribution)
  then the result is also a positive vector with unit `ℓ₁`-norm

-/

open Finset Function
open Matrix


namespace Stochastic

variable {R n : Type*} [Fintype n] [DecidableEq n]
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}
variable {x : n → R}

/--
A square matrix is row stochastic iff all entries are nonnegative, and right
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def rowStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1  }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    next => rw [← mulVec_mulVec, hN.2, hM.2]
  one_mem' := by
    simp [zero_le_one_elem]

lemma mem_rowStochastic :
    M ∈ rowStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧  M *ᵥ 1 = 1 :=
  Iff.rfl

/-- A square matrix is row stochastic if each element is non-negative and row sums to one. -/
lemma mem_rowStochastic_iff_sum :
    M ∈ rowStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ (∀ i, ∑ j, M i j = 1) := by
  simp [funext_iff, rowStochastic, mulVec, dotProduct]

/-- Every entry of a row stochastic matrix is nonnegative. -/
lemma nonneg_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each row sum of a row stochastic matrix is 1. -/
lemma sum_row_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) (i : n) : ∑ j, M i j = 1 :=
  (mem_rowStochastic_iff_sum.1 hM).2 _

/-- The all-ones column vector multiplied with a row stochastic matrix is 1. -/
lemma one_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) : M *ᵥ 1 = 1 :=
  (mem_rowStochastic.1 hM).2

/-- Every entry of a row stochastic matrix is less than or equal to 1. -/
lemma le_one_of_mem_rowStochastic (hM : M ∈ rowStochastic R n) {i j : n} :
    M i j ≤ 1 := by
  rw [← sum_row_of_mem_rowStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 _ k) (mem_univ j)


lemma vecMul_nonneg (hM : ∀ i j, 0 ≤ M i j) (hx : 0 ≤ x) : 0 ≤ x ᵥ* M :=
  fun j ↦ Finset.sum_nonneg fun i _ ↦ mul_nonneg (hx i) (hM i j)

lemma mulVec_nonneg (hM : ∀ i j, 0 ≤ M i j) (hx : 0 ≤ x) : 0 ≤ M *ᵥ x :=
  fun i ↦ Finset.sum_nonneg fun j _ ↦ mul_nonneg (hM i j) (hx j) 

/-- Left left-multiplication by row stochastic preserves `ℓ₁ norm` -/
lemma vecMul_dotProduct_one_eq_one_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : x ⬝ᵥ 1 = 1) : (x ᵥ* M) ⬝ᵥ 1 = 1 := by
  rw [← dotProduct_mulVec, hM.2, hx]

/--
A square matrix is column stochastic iff all entries are nonnegative, and left
multiplication by the vector of all 1s gives the vector of all 1s.
-/
def colStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ 1 ᵥ* M = 1  }
  mul_mem' {M N} hM hN := by
    refine Set.mem_sep ?_ ?_
    · intro i j
      apply Finset.sum_nonneg
      intro k _
      apply mul_nonneg
      · exact hM.1 i k
      · exact hN.1 k j
    · rw [← vecMul_vecMul, hM.2, hN.2]
  one_mem' := by
    simp [zero_le_one_elem]

lemma mem_colStochastic :
    M ∈ colStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧  1 ᵥ* M = 1 :=
  Iff.rfl

/-- A matrix is column stochastic if each column sums to one. -/
lemma mem_colStochastic_iff_sum :
    M ∈ colStochastic R n ↔
      (∀ i j, 0 ≤ M i j) ∧ (∀ j, ∑ i, M i j = 1) := by
  simp [funext_iff, colStochastic, vecMul, dotProduct]

/-- Every entry of a column stochastic matrix is nonnegative. -/
lemma nonneg_of_mem_colStochastic (hM : M ∈ colStochastic R n) {i j : n} : 0 ≤ M i j :=
  hM.1 _ _

/-- Each column sum of a column stochastic matrix is 1. -/
lemma sum_col_of_mem_colStochastic (hM : M ∈ colStochastic R n) (i : n) : ∑ j, M j i = 1 :=
  (mem_colStochastic_iff_sum.1 hM).2 _

/-- The all-ones column vector multiplied with a column stochastic matrix is 1. -/
lemma one_vecMul_of_mem_colStochastic (hM : M ∈ colStochastic R n) : 1 ᵥ* M = 1 :=
  (mem_colStochastic.1 hM).2

/-- Every entry of a column stochastic matrix is less than or equal to 1. -/
lemma le_one_of_mem_colStochastic (hM : M ∈ colStochastic R n) {i j : n} :
    M j i ≤ 1 := by
  rw [← sum_col_of_mem_colStochastic hM i]
  exact single_le_sum (fun k _ => hM.1 k _) (mem_univ j)

/-- Right multiplication of a column stochastic matrix by a non-negative vector
gives a non-negative vector. -/
lemma nonneg_mulVec_of_mem_colStochastic (hM : M ∈ colStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_colStochastic hM

/-- Left multiplication of a column stochastic matrix by a non-negative vector
gives a non-negative vector. -/
lemma nonneg_vecMul_of_mem_colStochastic (hM : M ∈ colStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg (hx k) ?_
  exact nonneg_of_mem_colStochastic hM

/-- Left left-multiplication by column stochastic preserves `ℓ₁ norm` -/
lemma mulVec_dotProduct_one_eq_one_colStochastic (hM : M ∈ colStochastic R n)
    (hx : 1 ⬝ᵥ x = 1) : 1  ⬝ᵥ (M  *ᵥ x) = 1 := by
  rw [dotProduct_mulVec, hM.2, hx]


/-- A matrix is column stochastic if and only if its transpose is row stochastic. -/
lemma colStochastic_iff_transpose_rowStochastic :
    M ∈ colStochastic R n ↔ Mᵀ ∈ rowStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_swap

end Stochastic

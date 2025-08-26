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

* `doublyStochastic_iff_rowStochastic_and_colStochastic` A matrix is doubly stochastic
  if and only if it is both row and column stochastic

-/

open Finset Function
open Matrix


namespace Stochastic

variable {R n : Type*} [Fintype n] [DecidableEq n]
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}
variable {x : n → R}

-- # rowStochastic

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


/-- Left multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector. -/
lemma nonneg_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

/-- Right multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector. -/
lemma nonneg_mulVec_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

/-- Left multiplication of a row stochastic matrix by a vector that is a
probability distribution gives a vector that is a probability distribution. -/
lemma pdist_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : (∀ i : n, 0 ≤ x i) ∧ ∑ i : n, x i = 1) :
    (∀ j : n, 0 ≤ (x ᵥ* M) j) ∧ ∑ j : n, (x ᵥ* M) j = 1 := by
  constructor
  · exact nonneg_vecMul_of_mem_rowStochastic hM hx.1
  · have h₀ : ∑ i : n, x i = x ⬝ᵥ 1 := by
      exact Eq.symm (dotProduct_one x)
    rw [h₀] at hx
    have h₁ : ∑ j : n, (x ᵥ* M) j = (x ᵥ* M) ⬝ᵥ 1 := by
      exact Eq.symm (dotProduct_one (x ᵥ* M))
    rw [h₁]
    have h₂ : x ᵥ* M ⬝ᵥ 1 = x ⬝ᵥ (M *ᵥ 1) := by
      rw [@dotProduct_mulVec]
    rw [h₂]
    have h₃ : M *ᵥ 1 = 1 := hM.2
    rw [h₃]
    exact hx.2


-- # colStochastic

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

/-- Right multiplication of a column stochastic matrix by a vector that is a
probability distribution gives a vector that is a probability distribution. -/
lemma pdist_mulVec_of_mem_colStochastic (hM : M ∈ colStochastic R n)
    (hx : (∀ i : n, 0 ≤ x i) ∧ ∑ i : n, x i = 1) :
    (∀ j : n, 0 ≤ (M *ᵥ x) j) ∧ ∑ j : n, (M *ᵥ x) j = 1 := by
  constructor
  · exact nonneg_mulVec_of_mem_colStochastic hM hx.1
  · have h₀ : ∑ i : n, x i = 1 ⬝ᵥ x := by
      exact Eq.symm (one_dotProduct x)
    rw [h₀] at hx
    have h₁ : ∑ j : n, (M *ᵥ x) j = 1 ⬝ᵥ (M *ᵥ x) := by
      exact Eq.symm (one_dotProduct (M *ᵥ x))
    rw [h₁]
    have h₂ : 1 ⬝ᵥ M *ᵥ x = (1 ᵥ* M) ⬝ᵥ x := dotProduct_mulVec 1 M x
    rw [h₂]
    have h₃ : 1 ᵥ* M = 1 := one_vecMul_of_mem_colStochastic hM
    rw [h₃]
    exact hx.2


/-- A matrix is column stochastic if and only if its transpose is row stochastic. -/
lemma colStochastic_iff_transpose_rowStochastic :
    M ∈ colStochastic R n ↔ Mᵀ ∈ rowStochastic R n := by
  constructor
  · intro hM
    have hM₁ : (∀ i j, 0 ≤ M i j) ∧ (∀ j, ∑ i, M i j = 1) := mem_colStochastic_iff_sum.mp hM
    have hM₂ : (∀ i, ∑ j, Mᵀ i j = 1) := by aesop
    have hM₃ : ∀ i j, 0 ≤ Mᵀ i j := by
      refine fun i j ↦ ?_
      have : ∀ i j, 0 ≤ M i j := hM.1
      aesop
    rw [mem_rowStochastic_iff_sum]
    exact ⟨hM₃, hM₂⟩
  · intro hM
    have hM₁ : (∀ i j, 0 ≤ Mᵀ i j) ∧ (∀ i, ∑ j, Mᵀ i j = 1) := mem_rowStochastic_iff_sum.mp hM
    have hM₂ : (∀ i, ∑ j, Mᵀ i j = 1) := by aesop
    have hM₃ : ∀ i j, 0 ≤ M i j := by
      refine fun i j ↦ ?_
      have : ∀ i j, 0 ≤ Mᵀ i j := hM.1
      aesop
    rw [mem_colStochastic_iff_sum]
    exact ⟨hM₃, hM₂⟩

end Stochastic

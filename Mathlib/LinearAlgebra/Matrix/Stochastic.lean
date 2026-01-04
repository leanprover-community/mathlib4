/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Row- and Column-stochastic matrices

A square matrix `M` is *row-stochastic* if all its entries are non-negative and `M *ᵥ 1 = 1`.
Likewise, `M` is *column-stochastic* if all its entries are non-negative and `1 ᵥ* M = 1`. This
file defines these concepts and provides basic API for them.

Note that *doubly stochastic* matrices (i.e. matrices that are both row- and column-stochastic)
are defined in `Analysis.Convex.DoublyStochasticMatrix`.

## Main definitions

* `rowStochastic`: row-stochastic matrices indexed by `n` with entries in `R`, as a submonoid
  of `Matrix n n R`.
* `colStochastic R n`: column-stochastic matrices indexed by `n` with entries in `R`, as a
  submonoid of `Matrix n n R`.

-/

@[expose] public section

open Finset

namespace Matrix

variable {R n : Type*} [Fintype n] [DecidableEq n]
variable [Semiring R] [PartialOrder R] [IsOrderedRing R] {M : Matrix n n R}
variable {x : n → R}

/- ## Row-stochastic matrices -/

/-- A square matrix is row stochastic iff all entries are nonnegative, and right
multiplication by the vector of all 1s gives the vector of all 1s. -/
def rowStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1  }
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun i _ => mul_nonneg (hM.1 _ _) (hN.1 _ _), ?_⟩
    next => rw [← mulVec_mulVec, hN.2, hM.2]
  one_mem' := by
    simp [zero_le_one_elem]

@[grind =]
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
gives a non-negative vector -/
lemma nonneg_vecMul_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (x ᵥ* M) j := by
  intro j
  simp only [Matrix.vecMul, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg (hx k)
  exact nonneg_of_mem_rowStochastic hM

/-- Right multiplication of a row stochastic matrix by a non-negative vector
gives a non-negative vector -/
lemma nonneg_mulVec_of_mem_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : ∀ i : n, 0 ≤ x i) : ∀ j : n, 0 ≤ (M *ᵥ x) j := by
  intro j
  simp only [Matrix.mulVec, dotProduct]
  apply Finset.sum_nonneg
  intro k _
  refine Left.mul_nonneg ?_ (hx k)
  exact nonneg_of_mem_rowStochastic hM

/-- Left left-multiplication by row stochastic preserves `ℓ₁ norm` -/
lemma vecMul_dotProduct_one_eq_one_rowStochastic (hM : M ∈ rowStochastic R n)
    (hx : x ⬝ᵥ 1 = 1) : (x ᵥ* M) ⬝ᵥ 1 = 1 := by
  rw [← dotProduct_mulVec, hM.2, hx]

/-- The set of row stochastic matrices is convex. -/
lemma convex_rowStochastic : Convex R (rowStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_rowStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is row stochastic. -/
@[simp, grind ←]
lemma permMatrix_mem_rowStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ rowStochastic R n := by
  rw [mem_rowStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply]


/- ## Column-stochastic matrices -/

/-- A square matrix is column stochastic iff all entries are nonnegative, and left
multiplication by the vector of all 1s gives the vector of all 1s. -/
def colStochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
    [IsOrderedRing R] : Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ 1 ᵥ* M = 1  }
  mul_mem' {M N} hM hN := by
    refine Set.mem_sep ?_ ?_
    · intro i j
      apply Finset.sum_nonneg
      grind [mul_nonneg]
    · rw [← vecMul_vecMul, hM.2, hN.2]
  one_mem' := by
    simp [zero_le_one_elem]

@[grind =]
lemma mem_colStochastic :
    M ∈ colStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ 1 ᵥ* M = 1 :=
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
    (hx : 1 ⬝ᵥ x = 1) : 1 ⬝ᵥ (M *ᵥ x) = 1 := by
  rw [dotProduct_mulVec, hM.2, hx]

/-- The set of column stochastic matrices is convex. -/
lemma convex_colStochastic : Convex R (colStochastic R n : Set (Matrix n n R)) := by
  intro x hx y hy a b ha hb h
  simp only [SetLike.mem_coe, mem_colStochastic_iff_sum] at hx hy ⊢
  simp [add_nonneg, ha, hb, mul_nonneg, hx, hy, sum_add_distrib, ← mul_sum, h]

/-- Any permutation matrix is column stochastic. -/
@[simp, grind ←]
lemma permMatrix_mem_colStochastic {σ : Equiv.Perm n} :
    σ.permMatrix R ∈ colStochastic R n := by
  rw [mem_colStochastic_iff_sum]
  refine ⟨fun i j => ?g1, ?g2⟩
  case g1 => aesop
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply]

/-- The transpose of a matrix is row stochastic matrix if it is column stochastic. -/
@[grind =]
lemma transpose_mem_rowStochastic_iff_mem_colStochastic :
    Mᵀ ∈ rowStochastic R n ↔ M ∈ colStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_swap

/-- The transpose of a matrix is column stochastic matrix if it is row stochastic. -/
@[grind =]
lemma transpose_mem_colStochastic_iff_mem_rowStochastic :
    Mᵀ ∈ colStochastic R n ↔ M ∈ rowStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_swap

end Matrix

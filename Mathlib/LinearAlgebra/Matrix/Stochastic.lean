/-
Copyright (c) 2025 Steven Herbert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Steven Herbert
-/
module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Matrix.Permutation

/-!
# Row- and Column-stochastic matrices

A square matrix `M` is *row-stochastic* if all its entries are non-negative and `M *ᵥ 1 = 1`.
Likewise, `M` is *column-stochastic* if all its entries are non-negative and `1 ᵥ* M = 1`. This
file defines these concepts and provides basic API for them.

Note that *doubly stochastic* matrices (i.e. matrices that are both row- and column-stochastic)
are defined in `Mathlib/Analysis/Convex/DoublyStochasticMatrix.lean`.

## Main definitions

* `rowStochastic`: row-stochastic matrices indexed by `n` with entries in `R`, as a submonoid
  of `Matrix n n R`.
* `colStochastic R n`: column-stochastic matrices indexed by `n` with entries in `R`, as a
  submonoid of `Matrix n n R`.

## Main results

* `Matrix.linfty_opNorm_le_one_of_mem_rowStochastic`: row-stochastic matrices have `L∞` operator
  norm at most `1` (`open scoped Matrix.Norms.Operator`).
* `Matrix.norm_mulVec_le_of_mem_rowStochastic`: hence they are nonexpansive for `mulVec`.
* `Matrix.spectralRadius_le_one_of_mem_rowStochastic`: their spectral radius is at most `1`.

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
    rw [← mulVec_mulVec, hN.2, hM.2]
  one_mem' := by
    simp [zero_le_one_elem]

lemma mem_rowStochastic :
    M ∈ rowStochastic R n ↔ (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 = 1 :=
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

/-- Applying a column-stochastic matrix to a vector preserves its sum. -/
lemma sum_mulVec_of_mem_colStochastic {M : Matrix n n R} {x : n → R}
    (hA : M ∈ colStochastic R n) : ∑ i, (M *ᵥ x) i = ∑ i, x i := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_comm]
  simp [sum_col_of_mem_colStochastic hA, ← Finset.sum_mul]

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
  case g2 => simp [Equiv.toPEquiv_apply, ← Equiv.eq_symm_apply σ]

/-- The transpose of a matrix is row stochastic matrix if it is column stochastic. -/
@[grind =]
lemma transpose_mem_rowStochastic_iff_mem_colStochastic :
    Mᵀ ∈ rowStochastic R n ↔ M ∈ colStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_comm

/-- The transpose of a matrix is column stochastic matrix if it is row stochastic. -/
@[grind =]
lemma transpose_mem_colStochastic_iff_mem_rowStochastic :
    Mᵀ ∈ colStochastic R n ↔ M ∈ rowStochastic R n := by
  simp only [mem_colStochastic_iff_sum, mem_rowStochastic_iff_sum, transpose_apply,
    and_congr_left_iff]
  exact fun _ ↦ forall_comm

/-- Reindexing a matrix preserves row-stochasticity. -/
@[aesop safe apply]
lemma reindex_mem_rowStochastic {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} (hM : M ∈ rowStochastic R n) : M.reindex e₁ e₂ ∈ rowStochastic R m :=
  ⟨fun _ _ ↦ by simpa using nonneg_of_mem_rowStochastic hM, by simp [submatrix_mulVec_equiv, hM.2]⟩

/-- Reindexing a matrix preserves row-stochasticity. -/
@[grind =]
lemma reindex_mem_rowStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ rowStochastic R m ↔ M ∈ rowStochastic R n := by
  refine ⟨fun h => ?_, reindex_mem_rowStochastic⟩
  have : M = (M.reindex e₁ e₂).reindex e₁.symm e₂.symm := by simp
  rw [this]
  exact reindex_mem_rowStochastic h

/-- Reindexing a matrix preserves column-stochasticity. -/
@[grind =]
lemma reindex_mem_colStochastic_iff {m : Type*} [Fintype m] [DecidableEq m] {M : Matrix n n R}
    {e₁ e₂ : n ≃ m} : M.reindex e₁ e₂ ∈ colStochastic R m ↔ M ∈ colStochastic R n := by
  rw [← transpose_transpose (reindex e₁ e₂ M), transpose_reindex,
    transpose_mem_colStochastic_iff_mem_rowStochastic, reindex_mem_rowStochastic_iff,
    ← transpose_mem_colStochastic_iff_mem_rowStochastic, transpose_transpose]

/-- Reindexing a matrix preserves column-stochasticity. -/
@[aesop safe apply]
alias ⟨_, reindex_mem_colStochastic⟩ := reindex_mem_colStochastic_iff

/-! ## Spectral radius

Results below use the `L∞` matrix operator norm.
-/

section SpectralRadius

open scoped Matrix.Norms.Operator

variable {A : Matrix n n ℝ}

omit [DecidableEq n] in
/-- Auxiliary form of `norm_mulVec_le_of_mem_rowStochastic` using row sums. -/
lemma norm_mulVec_le_of_row_sum (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) : ∀ v : n → ℝ, ‖A *ᵥ v‖ ≤ ‖v‖ := by
  intro v
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVec]
  calc |∑ j, A i j * v j|
    _ ≤ ∑ j, |A i j * v j| :=
      Finset.abs_sum_le_sum_abs (fun i_1 ↦ A i i_1 * v i_1) Finset.univ
    _ = ∑ j, (A i j) * |v j| := by simp_rw [abs_mul, abs_of_nonneg (h_nonneg i _)]
    _ ≤ ∑ j, A i j * ‖v‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (h_nonneg i j)
    _ = (∑ j, A i j) * ‖v‖ := (Finset.sum_mul ..).symm
    _ = ‖v‖ := by rw [h_row_sum i, one_mul]

/-- A row-stochastic matrix is nonexpansive for `mulVec` in the `L∞` operator norm.
Also `‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖` by `Matrix.linfty_opNorm_mulVec`. -/
lemma norm_mulVec_le_of_mem_rowStochastic (hM : A ∈ rowStochastic ℝ n) :
    ∀ v : n → ℝ, ‖A *ᵥ v‖ ≤ ‖v‖ := by
  rw [mem_rowStochastic_iff_sum] at hM
  exact norm_mulVec_le_of_row_sum hM.2 hM.1

/-- A row-stochastic matrix has `L∞` operator norm at most `1` (`Matrix.linfty_opNorm_def`). -/
lemma linfty_opNorm_le_one_of_mem_rowStochastic (hM : A ∈ rowStochastic ℝ n) : ‖A‖ ≤ 1 := by
  let f := ContinuousLinearMap.mk (Matrix.mulVecLin A)
  have h_mulVec : ∀ v, ‖f v‖ ≤ ‖v‖ := fun v => by
    dsimp [f]
    exact norm_mulVec_le_of_mem_rowStochastic hM v
  simpa [linfty_opNorm_eq_opNorm] using f.opNorm_le_bound zero_le_one fun v => by
    dsimp [f]
    rw [one_mul]
    exact h_mulVec v

/-- The spectral radius of a row-stochastic matrix is at most `1`, via
`spectrum.spectralRadius_le_nnnorm`. -/
theorem spectralRadius_le_one_of_mem_rowStochastic [Nonempty n] (hM : A ∈ rowStochastic ℝ n) :
    spectralRadius ℝ A ≤ 1 := by
  refine (spectrum.spectralRadius_le_nnnorm (𝕜 := ℝ) A).trans ?_
  rw [← ENNReal.coe_one]
  exact ENNReal.coe_le_coe.mpr (by simpa using linfty_opNorm_le_one_of_mem_rowStochastic hM)

/-- See `spectralRadius_le_one_of_mem_rowStochastic`. -/
theorem spectralRadius_le_one_of_row_sum [Nonempty n] (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) : spectralRadius ℝ A ≤ 1 :=
  spectralRadius_le_one_of_mem_rowStochastic (mem_rowStochastic_iff_sum.mpr ⟨h_nonneg, h_row_sum⟩)

end SpectralRadius

end Matrix

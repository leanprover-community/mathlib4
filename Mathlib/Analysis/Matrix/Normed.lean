/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Matrices as a normed space

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm (with `open scoped Matrix.Norms.Elementwise`):

  * `Matrix.seminormedAddCommGroup`
  * `Matrix.normedAddCommGroup`
  * `Matrix.normedSpace`
  * `Matrix.isBoundedSMul`
  * `Matrix.normSMulClass`

* The Frobenius norm (with `open scoped Matrix.Norms.Frobenius`):

  * `Matrix.frobeniusSeminormedAddCommGroup`
  * `Matrix.frobeniusNormedAddCommGroup`
  * `Matrix.frobeniusNormedSpace`
  * `Matrix.frobeniusNormedRing`
  * `Matrix.frobeniusNormedAlgebra`
  * `Matrix.frobeniusIsBoundedSMul`
  * `Matrix.frobeniusNormSMulClass`

* The $L^\infty$ operator norm (with `open scoped Matrix.Norms.Operator`):

  * `Matrix.linftyOpSeminormedAddCommGroup`
  * `Matrix.linftyOpNormedAddCommGroup`
  * `Matrix.linftyOpNormedSpace`
  * `Matrix.linftyOpIsBoundedSMul`
  * `Matrix.linftyOpNormSMulClass`
  * `Matrix.linftyOpNonUnitalSemiNormedRing`
  * `Matrix.linftyOpSemiNormedRing`
  * `Matrix.linftyOpNonUnitalNormedRing`
  * `Matrix.linftyOpNormedRing`
  * `Matrix.linftyOpNormedAlgebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.

The norm induced by the identification of `Matrix m n 𝕜` with
`EuclideanSpace n 𝕜 →L[𝕜] EuclideanSpace m 𝕜` (i.e., the ℓ² operator norm) can be found in
`Mathlib/Analysis/CStarAlgebra/Matrix.lean` and `open scoped Matrix.Norms.L2Operator`.
It is separated to avoid extraneous imports in this file.
-/

@[expose] public section

noncomputable section

open WithLp
open scoped NNReal Matrix

namespace Matrix

variable {R l m n α β ι : Type*} [Fintype l] [Fintype m] [Fintype n] [Unique ι]

/-! ### The elementwise supremum norm -/


section LinfLinf

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def seminormedAddCommGroup : SeminormedAddCommGroup (Matrix m n α) :=
  Pi.seminormedAddCommGroup

attribute [local instance] Matrix.seminormedAddCommGroup

theorem norm_def (A : Matrix m n α) : ‖A‖ = ‖fun i j => A i j‖ := rfl

/-- The norm of a matrix is the sup of the sup of the nnnorm of the entries -/
lemma norm_eq_sup_sup_nnnorm (A : Matrix m n α) :
    ‖A‖ = Finset.sup Finset.univ fun i ↦ Finset.sup Finset.univ fun j ↦ ‖A i j‖₊ := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]

theorem nnnorm_def (A : Matrix m n α) : ‖A‖₊ = ‖fun i j => A i j‖₊ := rfl

theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n α} : ‖A‖ ≤ r ↔ ∀ i j, ‖A i j‖ ≤ r := by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]

theorem nnnorm_le_iff {r : ℝ≥0} {A : Matrix m n α} : ‖A‖₊ ≤ r ↔ ∀ i j, ‖A i j‖₊ ≤ r := by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]

theorem norm_lt_iff {r : ℝ} (hr : 0 < r) {A : Matrix m n α} : ‖A‖ < r ↔ ∀ i j, ‖A i j‖ < r := by
  simp_rw [norm_def, pi_norm_lt_iff hr]

theorem nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : Matrix m n α} :
    ‖A‖₊ < r ↔ ∀ i j, ‖A i j‖₊ < r := by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]

theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖ ≤ ‖A‖ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖₊ ≤ ‖A‖₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)

@[simp]
theorem nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]

@[simp]
theorem norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) : ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]
theorem nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
  Finset.sup_comm _ _ _

@[simp]
theorem norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_transpose A

@[simp]
theorem nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose

@[simp]
theorem norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_conjTranspose A

instance [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨(le_of_eq <| norm_conjTranspose ·)⟩

@[simp]
theorem nnnorm_replicateCol (v : m → α) : ‖replicateCol ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]
theorem norm_replicateCol (v : m → α) : ‖replicateCol ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_replicateCol v

@[simp]
theorem nnnorm_replicateRow (v : n → α) : ‖replicateRow ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[simp]
theorem norm_replicateRow (v : n → α) : ‖replicateRow ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_replicateRow v

@[simp]
theorem nnnorm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  simp_rw [nnnorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine le_antisymm (Finset.sup_le fun j hj => ?_) ?_
  · obtain rfl | hij := eq_or_ne i j
    · rw [diagonal_apply_eq]
    · rw [diagonal_apply_ne _ hij, nnnorm_zero]
      exact zero_le _
  · refine Eq.trans_le ?_ (Finset.le_sup (Finset.mem_univ i))
    rw [diagonal_apply_eq]

@[simp]
theorem norm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_diagonal v

/-- Note this is safe as an instance as it carries no data. -/
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
  ⟨(norm_diagonal _).trans <| norm_one⟩

end SeminormedAddCommGroup

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  Pi.normedAddCommGroup

section NormedSpace

attribute [local instance] Matrix.seminormedAddCommGroup

/-- This applies to the sup norm of sup norm. -/
protected theorem isBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [IsBoundedSMul R α] : IsBoundedSMul R (Matrix m n α) :=
  Pi.instIsBoundedSMul

/-- This applies to the sup norm of sup norm. -/
protected theorem normSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [NormSMulClass R α] : NormSMulClass R (Matrix m n α) :=
  Pi.instNormSMulClass

variable [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  Pi.normedSpace

namespace Norms.Elementwise

attribute [scoped instance]
  Matrix.seminormedAddCommGroup
  Matrix.normedAddCommGroup
  Matrix.normedSpace
  Matrix.isBoundedSMul
  Matrix.normSMulClass

end Norms.Elementwise

end NormedSpace

end LinfLinf

/-! ### The $L_\infty$ operator norm

This section defines the matrix norm $\|A\|_\infty = \operatorname{sup}_i (\sum_j \|A_{ij}\|)$.

Note that this is equivalent to the operator norm, considering 
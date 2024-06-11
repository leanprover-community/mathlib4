/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
import Mathlib.Analysis.NormedSpace.PiLp
import Mathlib.Analysis.InnerProductSpace.PiL2

#align_import analysis.matrix from "leanprover-community/mathlib"@"46b633fd842bef9469441c0209906f6dddd2b4f5"

/-!
# Matrices as a normed space

In this file we provide the following non-instances for norms on matrices:

* The elementwise norm:

  * `Matrix.seminormedAddCommGroup`
  * `Matrix.normedAddCommGroup`
  * `Matrix.normedSpace`
  * `Matrix.boundedSMul`

* The Frobenius norm:

  * `Matrix.frobeniusSeminormedAddCommGroup`
  * `Matrix.frobeniusNormedAddCommGroup`
  * `Matrix.frobeniusNormedSpace`
  * `Matrix.frobeniusNormedRing`
  * `Matrix.frobeniusNormedAlgebra`
  * `Matrix.frobeniusBoundedSMul`

* The $L^\infty$ operator norm:

  * `Matrix.linftyOpSeminormedAddCommGroup`
  * `Matrix.linftyOpNormedAddCommGroup`
  * `Matrix.linftyOpNormedSpace`
  * `Matrix.linftyOpBoundedSMul`
  * `Matrix.linftyOpNonUnitalSemiNormedRing`
  * `Matrix.linftyOpSemiNormedRing`
  * `Matrix.linftyOpNonUnitalNormedRing`
  * `Matrix.linftyOpNormedRing`
  * `Matrix.linftyOpNormedAlgebra`

These are not declared as instances because there are several natural choices for defining the norm
of a matrix.

The norm induced by the identification of `Matrix m n 𝕜` with
`EuclideanSpace n 𝕜 →L[𝕜] EuclideanSpace m 𝕜` (i.e., the ℓ² operator norm) can be found in
`Analysis.NormedSpace.Star.Matrix`. It is separated to avoid extraneous imports in this file.
-/

noncomputable section

open scoped NNReal Matrix

namespace Matrix

variable {R l m n α β : Type*} [Fintype l] [Fintype m] [Fintype n]

/-! ### The elementwise supremum norm -/


section LinfLinf

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

/-- Seminormed group instance (using sup norm of sup norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def seminormedAddCommGroup : SeminormedAddCommGroup (Matrix m n α) :=
  Pi.seminormedAddCommGroup
#align matrix.seminormed_add_comm_group Matrix.seminormedAddCommGroup


attribute [local instance] Matrix.seminormedAddCommGroup

-- Porting note (#10756): new theorem (along with all the uses of this lemma below)
theorem norm_def (A : Matrix m n α) : ‖A‖ = ‖fun i j => A i j‖ := rfl

/-- The norm of a matrix is the sup of the sup of the nnnorm of the entries -/
lemma norm_eq_sup_sup_nnnorm (A : Matrix m n α) :
    ‖A‖ = Finset.sup Finset.univ fun i ↦ Finset.sup Finset.univ fun j ↦ ‖A i j‖₊ := by
  simp_rw [Matrix.norm_def, Pi.norm_def, Pi.nnnorm_def]

-- Porting note (#10756): new theorem (along with all the uses of this lemma below)
theorem nnnorm_def (A : Matrix m n α) : ‖A‖₊ = ‖fun i j => A i j‖₊ := rfl

theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) {A : Matrix m n α} : ‖A‖ ≤ r ↔ ∀ i j, ‖A i j‖ ≤ r := by
  simp_rw [norm_def, pi_norm_le_iff_of_nonneg hr]
#align matrix.norm_le_iff Matrix.norm_le_iff

theorem nnnorm_le_iff {r : ℝ≥0} {A : Matrix m n α} : ‖A‖₊ ≤ r ↔ ∀ i j, ‖A i j‖₊ ≤ r := by
  simp_rw [nnnorm_def, pi_nnnorm_le_iff]
#align matrix.nnnorm_le_iff Matrix.nnnorm_le_iff

theorem norm_lt_iff {r : ℝ} (hr : 0 < r) {A : Matrix m n α} : ‖A‖ < r ↔ ∀ i j, ‖A i j‖ < r := by
  simp_rw [norm_def, pi_norm_lt_iff hr]
#align matrix.norm_lt_iff Matrix.norm_lt_iff

theorem nnnorm_lt_iff {r : ℝ≥0} (hr : 0 < r) {A : Matrix m n α} :
    ‖A‖₊ < r ↔ ∀ i j, ‖A i j‖₊ < r := by
  simp_rw [nnnorm_def, pi_nnnorm_lt_iff hr]
#align matrix.nnnorm_lt_iff Matrix.nnnorm_lt_iff

theorem norm_entry_le_entrywise_sup_norm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖ ≤ ‖A‖ :=
  (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)
#align matrix.norm_entry_le_entrywise_sup_norm Matrix.norm_entry_le_entrywise_sup_norm

theorem nnnorm_entry_le_entrywise_sup_nnnorm (A : Matrix m n α) {i : m} {j : n} : ‖A i j‖₊ ≤ ‖A‖₊ :=
  (nnnorm_le_pi_nnnorm (A i) j).trans (nnnorm_le_pi_nnnorm A i)
#align matrix.nnnorm_entry_le_entrywise_sup_nnnorm Matrix.nnnorm_entry_le_entrywise_sup_nnnorm

@[simp]
theorem nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by
  simp only [nnnorm_def, Pi.nnnorm_def, Matrix.map_apply, hf]
#align matrix.nnnorm_map_eq Matrix.nnnorm_map_eq

@[simp]
theorem norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) : ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_map_eq A f fun a => Subtype.ext <| hf a : _)
#align matrix.norm_map_eq Matrix.norm_map_eq

@[simp]
theorem nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ :=
  Finset.sup_comm _ _ _
#align matrix.nnnorm_transpose Matrix.nnnorm_transpose

@[simp]
theorem norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_transpose A
#align matrix.norm_transpose Matrix.norm_transpose

@[simp]
theorem nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (nnnorm_map_eq _ _ nnnorm_star).trans A.nnnorm_transpose
#align matrix.nnnorm_conj_transpose Matrix.nnnorm_conjTranspose

@[simp]
theorem norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) : ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_conjTranspose A
#align matrix.norm_conj_transpose Matrix.norm_conjTranspose

instance [StarAddMonoid α] [NormedStarGroup α] : NormedStarGroup (Matrix m m α) :=
  ⟨norm_conjTranspose⟩

@[simp]
theorem nnnorm_col (v : m → α) : ‖col v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]
#align matrix.nnnorm_col Matrix.nnnorm_col

@[simp]
theorem norm_col (v : m → α) : ‖col v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_col v
#align matrix.norm_col Matrix.norm_col

@[simp]
theorem nnnorm_row (v : n → α) : ‖row v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]
#align matrix.nnnorm_row Matrix.nnnorm_row

@[simp]
theorem norm_row (v : n → α) : ‖row v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_row v
#align matrix.norm_row Matrix.norm_row

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
#align matrix.nnnorm_diagonal Matrix.nnnorm_diagonal

@[simp]
theorem norm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_diagonal v
#align matrix.norm_diagonal Matrix.norm_diagonal

/-- Note this is safe as an instance as it carries no data. -/
-- Porting note: not yet implemented: `@[nolint fails_quickly]`
instance [Nonempty n] [DecidableEq n] [One α] [NormOneClass α] : NormOneClass (Matrix n n α) :=
  ⟨(norm_diagonal _).trans <| norm_one⟩

end SeminormedAddCommGroup

/-- Normed group instance (using sup norm of sup norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  Pi.normedAddCommGroup
#align matrix.normed_add_comm_group Matrix.normedAddCommGroup

section NormedSpace

attribute [local instance] Matrix.seminormedAddCommGroup

/-- This applies to the sup norm of sup norm. -/
protected theorem boundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [BoundedSMul R α] : BoundedSMul R (Matrix m n α) :=
  Pi.instBoundedSMul

variable [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α]

/-- Normed space instance (using sup norm of sup norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
protected def normedSpace : NormedSpace R (Matrix m n α) :=
  Pi.normedSpace
#align matrix.normed_space Matrix.normedSpace

end NormedSpace

end LinfLinf

/-! ### The $L_\infty$ operator norm

This section defines the matrix norm $\|A\|_\infty = \operatorname{sup}_i (\sum_j \|A_{ij}\|)$.

Note that this is equivalent to the operator norm, considering $A$ as a linear map between two
$L^\infty$ spaces.
-/


section LinftyOp

/-- Seminormed group instance (using sup norm of L1 norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : SeminormedAddCommGroup (m → PiLp 1 fun j : n => α))
#align matrix.linfty_op_seminormed_add_comm_group Matrix.linftyOpSeminormedAddCommGroup

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedAddCommGroup [NormedAddCommGroup α] :
    NormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : NormedAddCommGroup (m → PiLp 1 fun j : n => α))
#align matrix.linfty_op_normed_add_comm_group Matrix.linftyOpNormedAddCommGroup

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
protected theorem linftyOpBoundedSMul
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [BoundedSMul R α] :
    BoundedSMul R (Matrix m n α) :=
  (by infer_instance : BoundedSMul R (m → PiLp 1 fun j : n => α))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by infer_instance : NormedSpace R (m → PiLp 1 fun j : n => α))
#align matrix.linfty_op_normed_space Matrix.linftyOpNormedSpace

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α]

theorem linfty_opNorm_def (A : Matrix m n α) :
    ‖A‖ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : ℝ≥0) := by
  -- Porting note: added
  change ‖fun i => (WithLp.equiv 1 _).symm (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_sum ENNReal.one_ne_top]
#align matrix.linfty_op_norm_def Matrix.linfty_opNorm_def

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_def := linfty_opNorm_def

theorem linfty_opNNNorm_def (A : Matrix m n α) :
    ‖A‖₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ :=
  Subtype.ext <| linfty_opNorm_def A
#align matrix.linfty_op_nnnorm_def Matrix.linfty_opNNNorm_def

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_def := linfty_opNNNorm_def

@[simp, nolint simpNF] -- Porting note: linter times out
theorem linfty_opNNNorm_col (v : m → α) : ‖col v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  simp
#align matrix.linfty_op_nnnorm_col Matrix.linfty_opNNNorm_col

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_col := linfty_opNNNorm_col

@[simp]
theorem linfty_opNorm_col (v : m → α) : ‖col v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_col v
#align matrix.linfty_op_norm_col Matrix.linfty_opNorm_col

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_col := linfty_opNorm_col

@[simp]
theorem linfty_opNNNorm_row (v : n → α) : ‖row v‖₊ = ∑ i, ‖v i‖₊ := by simp [linfty_opNNNorm_def]
#align matrix.linfty_op_nnnorm_row Matrix.linfty_opNNNorm_row

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_row := linfty_opNNNorm_row

@[simp]
theorem linfty_opNorm_row (v : n → α) : ‖row v‖ = ∑ i, ‖v i‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_row v).trans <| by simp [NNReal.coe_sum]
#align matrix.linfty_op_norm_row Matrix.linfty_opNorm_row

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_row := linfty_opNorm_row

@[simp]
theorem linfty_opNNNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]
#align matrix.linfty_op_nnnorm_diagonal Matrix.linfty_opNNNorm_diagonal

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_diagonal := linfty_opNNNorm_diagonal

@[simp]
theorem linfty_opNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_diagonal v
#align matrix.linfty_op_norm_diagonal Matrix.linfty_opNorm_diagonal

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_diagonal := linfty_opNorm_diagonal

end SeminormedAddCommGroup

section NonUnitalSeminormedRing

variable [NonUnitalSeminormedRing α]

theorem linfty_opNNNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [linfty_opNNNorm_def, Matrix.mul_apply]
  calc
    (Finset.univ.sup fun i => ∑ k, ‖∑ j, A i j * B j k‖₊) ≤
        Finset.univ.sup fun i => ∑ k, ∑ j, ‖A i j‖₊ * ‖B j k‖₊ :=
      Finset.sup_mono_fun fun i _hi =>
        Finset.sum_le_sum fun k _hk => nnnorm_sum_le_of_le _ fun j _hj => nnnorm_mul_le _ _
    _ = Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * ∑ k, ‖B j k‖₊ := by
      simp_rw [@Finset.sum_comm m, Finset.mul_sum]
    _ ≤ Finset.univ.sup fun i => ∑ j, ‖A i j‖₊ * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      refine Finset.sup_mono_fun fun i _hi => ?_
      gcongr with j hj
      exact Finset.le_sup (f := fun i ↦ ∑ k : n, ‖B i k‖₊) hj
    _ ≤ (Finset.univ.sup fun i => ∑ j, ‖A i j‖₊) * Finset.univ.sup fun i => ∑ j, ‖B i j‖₊ := by
      simp_rw [← Finset.sum_mul, ← NNReal.finset_sup_mul]
      rfl
#align matrix.linfty_op_nnnorm_mul Matrix.linfty_opNNNorm_mul

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_mul := linfty_opNNNorm_mul

theorem linfty_opNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNNNorm_mul _ _
#align matrix.linfty_op_norm_mul Matrix.linfty_opNorm_mul

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_mul := linfty_opNorm_mul

theorem linfty_opNNNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖₊ ≤ ‖A‖₊ * ‖v‖₊ := by
  rw [← linfty_opNNNorm_col (A *ᵥ v), ← linfty_opNNNorm_col v]
  exact linfty_opNNNorm_mul A (col v)
#align matrix.linfty_op_nnnorm_mul_vec Matrix.linfty_opNNNorm_mulVec

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_mulVec := linfty_opNNNorm_mulVec

theorem linfty_opNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖ :=
  linfty_opNNNorm_mulVec _ _
#align matrix.linfty_op_norm_mul_vec Matrix.linfty_opNorm_mulVec

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_mulVec := linfty_opNorm_mulVec

end NonUnitalSeminormedRing

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a semi normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[local instance]
protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSeminormedRing α] :
    NonUnitalSeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul := linfty_opNorm_mul }
#align matrix.linfty_op_non_unital_semi_normed_ring Matrix.linftyOpNonUnitalSemiNormedRing

/-- The `L₁-L∞` norm preserves one on non-empty matrices. Note this is safe as an instance, as it
carries no data. -/
instance linfty_opNormOneClass [SeminormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n] :
    NormOneClass (Matrix n n α) where norm_one := (linfty_opNorm_diagonal _).trans norm_one
#align matrix.linfty_op_norm_one_class Matrix.linfty_opNormOneClass

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a semi normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpSemiNormedRing [SeminormedRing α] [DecidableEq n] :
    SeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }
#align matrix.linfty_op_semi_normed_ring Matrix.linftyOpSemiNormedRing

/-- Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[local instance]
protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] :
    NonUnitalNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align matrix.linfty_op_non_unital_normed_ring Matrix.linftyOpNonUnitalNormedRing

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
  { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align matrix.linfty_op_normed_ring Matrix.linftyOpNormedRing

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedAlgebra [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
    [DecidableEq n] : NormedAlgebra R (Matrix n n α) :=
  { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }
#align matrix.linfty_op_normed_algebra Matrix.linftyOpNormedAlgebra


section
variable [NormedDivisionRing α] [NormedAlgebra ℝ α] [CompleteSpace α]

/-- Auxiliary construction; an element of norm 1 such that `a * unitOf a = ‖a‖`. -/
private def unitOf (a : α) : α := by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹

private theorem norm_unitOf (a : α) : ‖unitOf a‖₊ = 1 := by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul, nnnorm_inv, nnnorm_norm, mul_inv_cancel h]

set_option tactic.skipAssignedInstances false in
private theorem mul_unitOf (a : α) : a * unitOf a = algebraMap _ _ (‖a‖₊ : ℝ)  := by
  simp [unitOf]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel h, Algebra.algebraMap_eq_smul_one]

end

/-!
For a matrix over a field, the norm defined in this section agrees with the operator norm on
`ContinuousLinearMap`s between function types (which have the infinity norm).
-/
section
variable [NontriviallyNormedField α] [NormedAlgebra ℝ α]

lemma linfty_opNNNorm_eq_opNNNorm (A : Matrix m n α) :
    ‖A‖₊ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖₊ := by
  rw [ContinuousLinearMap.opNNNorm_eq_of_bounds _ (linfty_opNNNorm_mulVec _) fun N hN => ?_]
  rw [linfty_opNNNorm_def]
  refine Finset.sup_le fun i _ => ?_
  cases isEmpty_or_nonempty n
  · simp
  classical
  let x : n → α := fun j => unitOf (A i j)
  have hxn : ‖x‖₊ = 1 := by
    simp_rw [x, Pi.nnnorm_def, norm_unitOf, Finset.sup_const Finset.univ_nonempty]
  specialize hN x
  rw [hxn, mul_one, Pi.nnnorm_def, Finset.sup_le_iff] at hN
  replace hN := hN i (Finset.mem_univ _)
  dsimp [mulVec, dotProduct] at hN
  simp_rw [x, mul_unitOf, ← map_sum, nnnorm_algebraMap, ← NNReal.coe_sum, NNReal.nnnorm_eq,
    nnnorm_one, mul_one] at hN
  exact hN

@[deprecated (since := "2024-02-02")]
alias linfty_op_nnnorm_eq_op_nnnorm := linfty_opNNNorm_eq_opNNNorm

lemma linfty_opNorm_eq_opNorm (A : Matrix m n α) :
    ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_eq_op_norm := linfty_opNorm_eq_opNorm

variable [DecidableEq n]

@[simp] lemma linfty_opNNNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖₊ = ‖f‖₊ := by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']

@[deprecated (since := "2024-02-02")] alias linfty_op_nnnorm_toMatrix := linfty_opNNNorm_toMatrix

@[simp] lemma linfty_opNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖ = ‖f‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)

@[deprecated (since := "2024-02-02")] alias linfty_op_norm_toMatrix := linfty_opNorm_toMatrix

end

end LinftyOp

/-! ### The Frobenius norm

This is defined as $\|A\| = \sqrt{\sum_{i,j} \|A_{ij}\|^2}$.
When the matrix is over the real or complex numbers, this norm is submultiplicative.
-/


section frobenius

open scoped Matrix

/-- Seminormed group instance (using frobenius norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  inferInstanceAs (SeminormedAddCommGroup (PiLp 2 fun _i : m => PiLp 2 fun _j : n => α))
#align matrix.frobenius_seminormed_add_comm_group Matrix.frobeniusSeminormedAddCommGroup

/-- Normed group instance (using frobenius norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : NormedAddCommGroup (PiLp 2 fun i : m => PiLp 2 fun j : n => α))
#align matrix.frobenius_normed_add_comm_group Matrix.frobeniusNormedAddCommGroup

/-- This applies to the frobenius norm. -/
@[local instance]
theorem frobeniusBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [BoundedSMul R α] :
    BoundedSMul R (Matrix m n α) :=
  (by infer_instance : BoundedSMul R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

/-- Normed space instance (using frobenius norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by infer_instance : NormedSpace R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))
#align matrix.frobenius_normed_space Matrix.frobeniusNormedSpace

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

theorem frobenius_nnnorm_def (A : Matrix m n α) :
    ‖A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  -- Porting note: added, along with `WithLp.equiv_symm_pi_apply` below
  change ‖(WithLp.equiv 2 _).symm fun i => (WithLp.equiv 2 _).symm fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two,
    WithLp.equiv_symm_pi_apply]
#align matrix.frobenius_nnnorm_def Matrix.frobenius_nnnorm_def

theorem frobenius_norm_def (A : Matrix m n α) :
    ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) (frobenius_nnnorm_def A)).trans <| by simp [NNReal.coe_sum]
#align matrix.frobenius_norm_def Matrix.frobenius_norm_def

@[simp]
theorem frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]
#align matrix.frobenius_nnnorm_map_eq Matrix.frobenius_nnnorm_map_eq

@[simp]
theorem frobenius_norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) :
    ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a : _)
#align matrix.frobenius_norm_map_eq Matrix.frobenius_norm_map_eq

@[simp]
theorem frobenius_nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ := by
  rw [frobenius_nnnorm_def, frobenius_nnnorm_def, Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]  -- Porting note: added
#align matrix.frobenius_nnnorm_transpose Matrix.frobenius_nnnorm_transpose

@[simp]
theorem frobenius_norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_transpose A
#align matrix.frobenius_norm_transpose Matrix.frobenius_norm_transpose

@[simp]
theorem frobenius_nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose
#align matrix.frobenius_nnnorm_conj_transpose Matrix.frobenius_nnnorm_conjTranspose

@[simp]
theorem frobenius_norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_conjTranspose A
#align matrix.frobenius_norm_conj_transpose Matrix.frobenius_norm_conjTranspose

instance frobenius_normedStarGroup [StarAddMonoid α] [NormedStarGroup α] :
    NormedStarGroup (Matrix m m α) :=
  ⟨frobenius_norm_conjTranspose⟩
#align matrix.frobenius_normed_star_group Matrix.frobenius_normedStarGroup

@[simp]
theorem frobenius_norm_row (v : m → α) : ‖row v‖ = ‖(WithLp.equiv 2 _).symm v‖ := by
  rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [row_apply, Real.rpow_two, WithLp.equiv_symm_pi_apply]
#align matrix.frobenius_norm_row Matrix.frobenius_norm_row

@[simp]
theorem frobenius_nnnorm_row (v : m → α) : ‖row v‖₊ = ‖(WithLp.equiv 2 _).symm v‖₊ :=
  Subtype.ext <| frobenius_norm_row v
#align matrix.frobenius_nnnorm_row Matrix.frobenius_nnnorm_row

@[simp]
theorem frobenius_norm_col (v : n → α) : ‖col v‖ = ‖(WithLp.equiv 2 _).symm v‖ := by
  simp_rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [col_apply, Real.rpow_two, WithLp.equiv_symm_pi_apply]
#align matrix.frobenius_norm_col Matrix.frobenius_norm_col

@[simp]
theorem frobenius_nnnorm_col (v : n → α) : ‖col v‖₊ = ‖(WithLp.equiv 2 _).symm v‖₊ :=
  Subtype.ext <| frobenius_norm_col v
#align matrix.frobenius_nnnorm_col Matrix.frobenius_nnnorm_col

@[simp]
theorem frobenius_nnnorm_diagonal [DecidableEq n] (v : n → α) :
    ‖diagonal v‖₊ = ‖(WithLp.equiv 2 _).symm v‖₊ := by
  simp_rw [frobenius_nnnorm_def, ← Finset.sum_product', Finset.univ_product_univ,
    PiLp.nnnorm_eq_of_L2]
  let s := (Finset.univ : Finset n).map ⟨fun i : n => (i, i), fun i j h => congr_arg Prod.fst h⟩
  rw [← Finset.sum_subset (Finset.subset_univ s) fun i _hi his => ?_]
  · rw [Finset.sum_map, NNReal.sqrt_eq_rpow]
    dsimp
    simp_rw [diagonal_apply_eq, NNReal.rpow_two]
  · suffices i.1 ≠ i.2 by rw [diagonal_apply_ne _ this, nnnorm_zero, NNReal.zero_rpow two_ne_zero]
    intro h
    exact Finset.mem_map.not.mp his ⟨i.1, Finset.mem_univ _, Prod.ext rfl h⟩
#align matrix.frobenius_nnnorm_diagonal Matrix.frobenius_nnnorm_diagonal

@[simp]
theorem frobenius_norm_diagonal [DecidableEq n] (v : n → α) :
    ‖diagonal v‖ = ‖(WithLp.equiv 2 _).symm v‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_diagonal v : _).trans rfl
#align matrix.frobenius_norm_diagonal Matrix.frobenius_norm_diagonal

end SeminormedAddCommGroup

theorem frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] :
    ‖(1 : Matrix n n α)‖₊ = NNReal.sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
  refine (frobenius_nnnorm_diagonal _).trans ?_
  -- Porting note: change to erw, since `fun x => 1` no longer matches `Function.const`
  erw [PiLp.nnnorm_equiv_symm_const ENNReal.two_ne_top]
  simp_rw [NNReal.sqrt_eq_rpow]
  -- Porting note: added `ENNReal.toReal_ofNat`
  simp only [ENNReal.toReal_div, ENNReal.one_toReal, ENNReal.toReal_ofNat]
#align matrix.frobenius_nnnorm_one Matrix.frobenius_nnnorm_one

section RCLike

variable [RCLike α]

theorem frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow, @Finset.sum_comm _ _ m, Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos, ← NNReal.rpow_mul,
    mul_div_cancel₀ (1 : ℝ) two_ne_zero, NNReal.rpow_one, NNReal.mul_rpow]
  have :=
    @nnnorm_inner_le_nnnorm α _ _ _ _ ((WithLp.equiv 2 <| _ → α).symm fun j => star (A i j))
      ((WithLp.equiv 2 <| _ → α).symm fun k => B k j)
  simpa only [WithLp.equiv_symm_pi_apply, PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply,
    Pi.nnnorm_def, PiLp.nnnorm_eq_of_L2, star_star, nnnorm_star, NNReal.sqrt_eq_rpow,
    NNReal.rpow_two] using this
#align matrix.frobenius_nnnorm_mul Matrix.frobenius_nnnorm_mul

theorem frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  frobenius_nnnorm_mul A B
#align matrix.frobenius_norm_mul Matrix.frobenius_norm_mul

/-- Normed ring instance (using frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
  { Matrix.frobeniusSeminormedAddCommGroup, Matrix.instRing with
    norm := Norm.norm
    norm_mul := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }
#align matrix.frobenius_normed_ring Matrix.frobeniusNormedRing

/-- Normed algebra instance (using frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] :
    NormedAlgebra R (Matrix m m α) :=
  { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }
#align matrix.frobenius_normed_algebra Matrix.frobeniusNormedAlgebra

end RCLike

end frobenius

end Matrix

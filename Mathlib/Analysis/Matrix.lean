/-
Copyright (c) 2021 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth, Eric Wieser
-/
import Mathlib.Analysis.InnerProductSpace.PiL2

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

@[deprecated (since := "2025-03-20")] alias nnnorm_col := nnnorm_replicateCol

@[simp]
theorem norm_replicateCol (v : m → α) : ‖replicateCol ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_replicateCol v

@[deprecated (since := "2025-03-20")] alias norm_col := norm_replicateCol

@[simp]
theorem nnnorm_replicateRow (v : n → α) : ‖replicateRow ι v‖₊ = ‖v‖₊ := by
  simp [nnnorm_def, Pi.nnnorm_def]

@[deprecated (since := "2025-03-20")] alias nnnorm_row := nnnorm_replicateRow

@[simp]
theorem norm_replicateRow (v : n → α) : ‖replicateRow ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| nnnorm_replicateRow v

@[deprecated (since := "2025-03-20")] alias norm_row := norm_replicateRow

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

@[deprecated (since := "2025-03-10")] protected alias boundedSMul := Matrix.isBoundedSMul

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

/-- Normed group instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedAddCommGroup [NormedAddCommGroup α] :
    NormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : NormedAddCommGroup (m → PiLp 1 fun j : n => α))

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
protected theorem linftyOpIsBoundedSMul
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [IsBoundedSMul R α] :
    IsBoundedSMul R (Matrix m n α) :=
  (by infer_instance : IsBoundedSMul R (m → PiLp 1 fun j : n => α))

/-- This applies to the sup norm of L1 norm. -/
@[local instance]
protected theorem linftyOpNormSMulClass
    [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α] [NormSMulClass R α] :
    NormSMulClass R (Matrix m n α) :=
  (by infer_instance : NormSMulClass R (m → PiLp 1 fun j : n => α))

/-- Normed space instance (using sup norm of L1 norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by infer_instance : NormedSpace R (m → PiLp 1 fun j : n => α))

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α]

theorem linfty_opNorm_def (A : Matrix m n α) :
    ‖A‖ = ((Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ : ℝ≥0) := by
  change ‖fun i => toLp 1 (A i)‖ = _
  simp [Pi.norm_def, PiLp.nnnorm_eq_of_L1]

theorem linfty_opNNNorm_def (A : Matrix m n α) :
    ‖A‖₊ = (Finset.univ : Finset m).sup fun i : m => ∑ j : n, ‖A i j‖₊ :=
  Subtype.ext <| linfty_opNorm_def A

@[simp]
theorem linfty_opNNNorm_replicateCol (v : m → α) : ‖replicateCol ι v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  simp

@[deprecated (since := "2025-03-20")] alias linfty_opNNNorm_col := linfty_opNNNorm_replicateCol

@[simp]
theorem linfty_opNorm_replicateCol (v : m → α) : ‖replicateCol ι v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_replicateCol v

@[deprecated (since := "2025-03-20")] alias linfty_opNorm_col := linfty_opNorm_replicateCol

@[simp]
theorem linfty_opNNNorm_replicateRow (v : n → α) : ‖replicateRow ι v‖₊ = ∑ i, ‖v i‖₊ := by
  simp [linfty_opNNNorm_def]

@[deprecated (since := "2025-03-20")] alias linfty_opNNNorm_row := linfty_opNNNorm_replicateRow

@[simp]
theorem linfty_opNorm_replicateRow (v : n → α) : ‖replicateRow ι v‖ = ∑ i, ‖v i‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_replicateRow v).trans <| by simp [NNReal.coe_sum]

@[deprecated (since := "2025-03-20")] alias linfty_opNorm_row := linfty_opNNNorm_replicateRow

@[simp]
theorem linfty_opNNNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖₊ = ‖v‖₊ := by
  rw [linfty_opNNNorm_def, Pi.nnnorm_def]
  congr 1 with i : 1
  refine (Finset.sum_eq_single_of_mem _ (Finset.mem_univ i) fun j _hj hij => ?_).trans ?_
  · rw [diagonal_apply_ne' _ hij, nnnorm_zero]
  · rw [diagonal_apply_eq]

@[simp]
theorem linfty_opNorm_diagonal [DecidableEq m] (v : m → α) : ‖diagonal v‖ = ‖v‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| linfty_opNNNorm_diagonal v

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

theorem linfty_opNorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  linfty_opNNNorm_mul _ _

theorem linfty_opNNNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖₊ ≤ ‖A‖₊ * ‖v‖₊ := by
  rw [← linfty_opNNNorm_replicateCol (ι := Fin 1) (A *ᵥ v),
    ← linfty_opNNNorm_replicateCol v (ι := Fin 1)]
  exact linfty_opNNNorm_mul A (replicateCol (Fin 1) v)

theorem linfty_opNorm_mulVec (A : Matrix l m α) (v : m → α) : ‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖ :=
  linfty_opNNNorm_mulVec _ _

end NonUnitalSeminormedRing

/-- Seminormed non-unital ring instance (using sup norm of L1 norm) for matrices over a semi normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[local instance]
protected def linftyOpNonUnitalSemiNormedRing [NonUnitalSeminormedRing α] :
    NonUnitalSeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpSeminormedAddCommGroup, Matrix.instNonUnitalRing with
    norm_mul_le := linfty_opNorm_mul }

/-- The `L₁-L∞` norm preserves one on non-empty matrices. Note this is safe as an instance, as it
carries no data. -/
instance linfty_opNormOneClass [SeminormedRing α] [NormOneClass α] [DecidableEq n] [Nonempty n] :
    NormOneClass (Matrix n n α) where norm_one := (linfty_opNorm_diagonal _).trans norm_one

/-- Seminormed ring instance (using sup norm of L1 norm) for matrices over a semi normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpSemiNormedRing [SeminormedRing α] [DecidableEq n] :
    SeminormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing, Matrix.instRing with }

/-- Normed non-unital ring instance (using sup norm of L1 norm) for matrices over a normed
non-unital ring. Not declared as an instance because there are several natural choices for defining
the norm of a matrix. -/
@[local instance]
protected def linftyOpNonUnitalNormedRing [NonUnitalNormedRing α] :
    NonUnitalNormedRing (Matrix n n α) :=
  { Matrix.linftyOpNonUnitalSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed ring instance (using sup norm of L1 norm) for matrices over a normed ring.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedRing [NormedRing α] [DecidableEq n] : NormedRing (Matrix n n α) :=
  { Matrix.linftyOpSemiNormedRing with
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed algebra instance (using sup norm of L1 norm) for matrices over a normed algebra. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
protected def linftyOpNormedAlgebra [NormedField R] [SeminormedRing α] [NormedAlgebra R α]
    [DecidableEq n] : NormedAlgebra R (Matrix n n α) :=
  { Matrix.linftyOpNormedSpace, Matrix.instAlgebra with }


section
variable [NormedDivisionRing α] [NormedAlgebra ℝ α]

/-- Auxiliary construction; an element of norm 1 such that `a * unitOf a = ‖a‖`. -/
private def unitOf (a : α) : α := by classical exact if a = 0 then 1 else ‖a‖ • a⁻¹

private theorem norm_unitOf (a : α) : ‖unitOf a‖₊ = 1 := by
  rw [unitOf]
  split_ifs with h
  · simp
  · rw [← nnnorm_eq_zero] at h
    rw [nnnorm_smul, nnnorm_inv, nnnorm_norm, mul_inv_cancel₀ h]

private theorem mul_unitOf (a : α) : a * unitOf a = algebraMap _ _ (‖a‖₊ : ℝ)  := by
  simp only [unitOf, coe_nnnorm]
  split_ifs with h
  · simp [h]
  · rw [mul_smul_comm, mul_inv_cancel₀ h, Algebra.algebraMap_eq_smul_one]

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

lemma linfty_opNorm_eq_opNorm (A : Matrix m n α) :
    ‖A‖ = ‖ContinuousLinearMap.mk (Matrix.mulVecLin A)‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_eq_opNNNorm A)

variable [DecidableEq n]

@[simp] lemma linfty_opNNNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖₊ = ‖f‖₊ := by
  rw [linfty_opNNNorm_eq_opNNNorm]
  simp only [← toLin'_apply', toLin'_toMatrix']

@[simp] lemma linfty_opNorm_toMatrix (f : (n → α) →L[α] (m → α)) :
    ‖LinearMap.toMatrix' (↑f : (n → α) →ₗ[α] (m → α))‖ = ‖f‖ :=
  congr_arg NNReal.toReal (linfty_opNNNorm_toMatrix f)

end

namespace Norms.Operator
attribute [scoped instance]
  Matrix.linftyOpSeminormedAddCommGroup
  Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedSpace
  Matrix.linftyOpIsBoundedSMul
  Matrix.linftyOpNormSMulClass
  Matrix.linftyOpNonUnitalSemiNormedRing
  Matrix.linftyOpSemiNormedRing
  Matrix.linftyOpNonUnitalNormedRing
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra
end Norms.Operator

end LinftyOp

/-! ### The Frobenius norm

This is defined as $\|A\| = \sqrt{\sum_{i,j} \|A_{ij}\|^2}$.
When the matrix is over the real or complex numbers, this norm is submultiplicative.
-/


section frobenius

open scoped Matrix

/-- Seminormed group instance (using the Frobenius norm) for matrices over a seminormed group. Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusSeminormedAddCommGroup [SeminormedAddCommGroup α] :
    SeminormedAddCommGroup (Matrix m n α) :=
  inferInstanceAs (SeminormedAddCommGroup (PiLp 2 fun _i : m => PiLp 2 fun _j : n => α))

/-- Normed group instance (using the Frobenius norm) for matrices over a normed group.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedAddCommGroup [NormedAddCommGroup α] : NormedAddCommGroup (Matrix m n α) :=
  (by infer_instance : NormedAddCommGroup (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

/-- This applies to the Frobenius norm. -/
@[local instance]
theorem frobeniusIsBoundedSMul [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [IsBoundedSMul R α] :
    IsBoundedSMul R (Matrix m n α) :=
  (by infer_instance : IsBoundedSMul R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

/-- This applies to the Frobenius norm. -/
@[local instance]
theorem frobeniusNormSMulClass [SeminormedRing R] [SeminormedAddCommGroup α] [Module R α]
    [NormSMulClass R α] :
    NormSMulClass R (Matrix m n α) :=
  (by infer_instance : NormSMulClass R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

@[deprecated (since := "2025-03-10")] alias frobeniusBoundedSMul := frobeniusIsBoundedSMul

/-- Normed space instance (using the Frobenius norm) for matrices over a normed space.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedSpace [NormedField R] [SeminormedAddCommGroup α] [NormedSpace R α] :
    NormedSpace R (Matrix m n α) :=
  (by infer_instance : NormedSpace R (PiLp 2 fun i : m => PiLp 2 fun j : n => α))

section SeminormedAddCommGroup

variable [SeminormedAddCommGroup α] [SeminormedAddCommGroup β]

theorem frobenius_nnnorm_def (A : Matrix m n α) :
    ‖A‖₊ = (∑ i, ∑ j, ‖A i j‖₊ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  change ‖toLp 2 fun i => toLp 2 fun j => A i j‖₊ = _
  simp_rw [PiLp.nnnorm_eq_of_L2, NNReal.sq_sqrt, NNReal.sqrt_eq_rpow, NNReal.rpow_two,
    PiLp.toLp_apply]

theorem frobenius_norm_def (A : Matrix m n α) :
    ‖A‖ = (∑ i, ∑ j, ‖A i j‖ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) (frobenius_nnnorm_def A)).trans <| by simp [NNReal.coe_sum]

@[simp]
theorem frobenius_nnnorm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖₊ = ‖a‖₊) :
    ‖A.map f‖₊ = ‖A‖₊ := by simp_rw [frobenius_nnnorm_def, Matrix.map_apply, hf]

@[simp]
theorem frobenius_norm_map_eq (A : Matrix m n α) (f : α → β) (hf : ∀ a, ‖f a‖ = ‖a‖) :
    ‖A.map f‖ = ‖A‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_map_eq A f fun a => Subtype.ext <| hf a :)

@[simp]
theorem frobenius_nnnorm_transpose (A : Matrix m n α) : ‖Aᵀ‖₊ = ‖A‖₊ := by
  rw [frobenius_nnnorm_def, frobenius_nnnorm_def, Finset.sum_comm]
  simp_rw [Matrix.transpose_apply]

@[simp]
theorem frobenius_norm_transpose (A : Matrix m n α) : ‖Aᵀ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_transpose A

@[simp]
theorem frobenius_nnnorm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖₊ = ‖A‖₊ :=
  (frobenius_nnnorm_map_eq _ _ nnnorm_star).trans A.frobenius_nnnorm_transpose

@[simp]
theorem frobenius_norm_conjTranspose [StarAddMonoid α] [NormedStarGroup α] (A : Matrix m n α) :
    ‖Aᴴ‖ = ‖A‖ :=
  congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_conjTranspose A

instance frobenius_normedStarGroup [StarAddMonoid α] [NormedStarGroup α] :
    NormedStarGroup (Matrix m m α) :=
  ⟨(le_of_eq <| frobenius_norm_conjTranspose ·)⟩

@[simp]
lemma frobenius_norm_replicateRow (v : m → α) : ‖replicateRow ι v‖ = ‖toLp 2 v‖ := by
  rw [frobenius_norm_def, Fintype.sum_unique, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]
  simp only [replicateRow_apply, Real.rpow_two, PiLp.toLp_apply]

@[deprecated (since := "2025-03-20")] alias frobenius_norm_row := frobenius_norm_replicateRow

@[simp]
lemma frobenius_nnnorm_replicateRow (v : m → α) : ‖replicateRow ι v‖₊ = ‖toLp 2 v‖₊ :=
  Subtype.ext <| frobenius_norm_replicateRow v

@[deprecated (since := "2025-03-20")] alias frobenius_nnnorm_row := frobenius_nnnorm_replicateRow

@[simp]
lemma frobenius_norm_replicateCol (v : n → α) : ‖replicateCol ι v‖ = ‖toLp 2 v‖ := by
  simp [frobenius_norm_def, PiLp.norm_eq_of_L2, Real.sqrt_eq_rpow]

@[deprecated (since := "2025-03-20")] alias frobenius_norm_col := frobenius_norm_replicateCol

@[simp]
lemma frobenius_nnnorm_replicateCol (v : n → α) : ‖replicateCol ι v‖₊ = ‖toLp 2 v‖₊ :=
  Subtype.ext <| frobenius_norm_replicateCol v

@[deprecated (since := "2025-03-20")] alias frobenius_nnnorm_col := frobenius_nnnorm_replicateCol

@[simp]
lemma frobenius_nnnorm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖₊ = ‖toLp 2 v‖₊ := by
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

@[simp]
lemma frobenius_norm_diagonal [DecidableEq n] (v : n → α) : ‖diagonal v‖ = ‖toLp 2 v‖ :=
  (congr_arg ((↑) : ℝ≥0 → ℝ) <| frobenius_nnnorm_diagonal v :).trans rfl

end SeminormedAddCommGroup

theorem frobenius_nnnorm_one [DecidableEq n] [SeminormedAddCommGroup α] [One α] :
    ‖(1 : Matrix n n α)‖₊ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
  calc
    ‖(diagonal 1 : Matrix n n α)‖₊
    _ = ‖toLp 2 (Function.const _ 1)‖₊ := frobenius_nnnorm_diagonal _
    _ = .sqrt (Fintype.card n) * ‖(1 : α)‖₊ := by
      rw [PiLp.nnnorm_toLp_const (ENNReal.ofNat_ne_top (n := 2))]
      simp [NNReal.sqrt_eq_rpow]

section RCLike

variable [RCLike α]

theorem frobenius_nnnorm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖₊ ≤ ‖A‖₊ * ‖B‖₊ := by
  simp_rw [frobenius_nnnorm_def, Matrix.mul_apply]
  rw [← NNReal.mul_rpow, @Finset.sum_comm _ _ m, Finset.sum_mul_sum]
  gcongr with i _ j
  rw [← NNReal.rpow_le_rpow_iff one_half_pos, ← NNReal.rpow_mul,
    mul_div_cancel₀ (1 : ℝ) two_ne_zero, NNReal.rpow_one, NNReal.mul_rpow]
  simpa only [PiLp.toLp_apply, PiLp.inner_apply, RCLike.inner_apply', starRingEnd_apply,
    Pi.nnnorm_def, PiLp.nnnorm_eq_of_L2, star_star, nnnorm_star, NNReal.sqrt_eq_rpow,
    NNReal.rpow_two] using nnnorm_inner_le_nnnorm (𝕜 := α) (toLp 2 (star <| A i ·)) (toLp 2 (B · j))

theorem frobenius_norm_mul (A : Matrix l m α) (B : Matrix m n α) : ‖A * B‖ ≤ ‖A‖ * ‖B‖ :=
  frobenius_nnnorm_mul A B

/-- Normed ring instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedRing [DecidableEq m] : NormedRing (Matrix m m α) :=
  { Matrix.instRing, Matrix.frobeniusSeminormedAddCommGroup with
    norm_mul_le := frobenius_norm_mul
    eq_of_dist_eq_zero := eq_of_dist_eq_zero }

/-- Normed algebra instance (using the Frobenius norm) for matrices over `ℝ` or `ℂ`.  Not
declared as an instance because there are several natural choices for defining the norm of a
matrix. -/
@[local instance]
def frobeniusNormedAlgebra [DecidableEq m] [NormedField R] [NormedAlgebra R α] :
    NormedAlgebra R (Matrix m m α) :=
  { Matrix.frobeniusNormedSpace, Matrix.instAlgebra with }

end RCLike

end frobenius

namespace Norms.Frobenius
attribute [scoped instance]
  Matrix.frobeniusSeminormedAddCommGroup
  Matrix.frobeniusNormedAddCommGroup
  Matrix.frobeniusNormedSpace
  Matrix.frobeniusNormedRing
  Matrix.frobeniusNormedAlgebra
  Matrix.frobeniusIsBoundedSMul
  Matrix.frobeniusNormSMulClass
end Norms.Frobenius

end Matrix

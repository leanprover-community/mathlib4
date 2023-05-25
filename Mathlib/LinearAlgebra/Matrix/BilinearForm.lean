/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying

! This file was ported from Lean 3 source module linear_algebra.matrix.bilinear_form
! leanprover-community/mathlib commit 075b3f7d19b9da85a0b54b3e33055a74fc388dec
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.LinearAlgebra.Matrix.Basis
import Mathbin.LinearAlgebra.Matrix.Nondegenerate
import Mathbin.LinearAlgebra.Matrix.NonsingularInverse
import Mathbin.LinearAlgebra.Matrix.ToLinearEquiv
import Mathbin.LinearAlgebra.BilinearForm
import Mathbin.LinearAlgebra.Matrix.SesquilinearForm

/-!
# Bilinear form

This file defines the conversion between bilinear forms and matrices.

## Main definitions

 * `matrix.to_bilin` given a basis define a bilinear form
 * `matrix.to_bilin'` define the bilinear form on `n → R`
 * `bilin_form.to_matrix`: calculate the matrix coefficients of a bilinear form
 * `bilin_form.to_matrix'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Notations

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## Tags

bilinear_form, matrix, basis

-/


variable {R : Type _} {M : Type _} [Semiring R] [AddCommMonoid M] [Module R M]

variable {R₁ : Type _} {M₁ : Type _} [Ring R₁] [AddCommGroup M₁] [Module R₁ M₁]

variable {R₂ : Type _} {M₂ : Type _} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]

variable {R₃ : Type _} {M₃ : Type _} [CommRing R₃] [AddCommGroup M₃] [Module R₃ M₃]

variable {V : Type _} {K : Type _} [Field K] [AddCommGroup V] [Module K V]

variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

section Matrix

variable {n o : Type _}

open BigOperators

open BilinForm Finset LinearMap Matrix

open Matrix

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
/-- The map from `matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₂) : BilinForm R₂ (n → R₂)
    where
  bilin v w := ∑ (i) (j), v i * M i j * w j
  bilin_add_left x y z := by simp only [Pi.add_apply, add_mul, sum_add_distrib]
  bilin_smul_left a x y := by simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]
  bilin_add_right x y z := by simp only [Pi.add_apply, mul_add, sum_add_distrib]
  bilin_smul_right a x y := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, mul_left_comm, mul_sum]
#align matrix.to_bilin'_aux Matrix.toBilin'Aux

theorem Matrix.toBilin'Aux_stdBasis [Fintype n] [DecidableEq n] (M : Matrix n n R₂) (i j : n) :
    M.toBilin'Aux (stdBasis R₂ (fun _ => R₂) i 1) (stdBasis R₂ (fun _ => R₂) j 1) = M i j :=
  by
  rw [Matrix.toBilin'Aux, coe_fn_mk, sum_eq_single i, sum_eq_single j]
  · simp only [std_basis_same, std_basis_same, one_mul, mul_one]
  · rintro j' - hj'
    apply mul_eq_zero_of_right
    exact std_basis_ne R₂ (fun _ => R₂) _ _ hj' 1
  · intros
    have := Finset.mem_univ j
    contradiction
  · rintro i' - hi'
    refine' Finset.sum_eq_zero fun j _ => _
    apply mul_eq_zero_of_left
    apply mul_eq_zero_of_left
    exact std_basis_ne R₂ (fun _ => R₂) _ _ hi' 1
  · intros
    have := Finset.mem_univ i
    contradiction
#align matrix.to_bilin'_aux_std_basis Matrix.toBilin'Aux_stdBasis

/-- The linear map from bilinear forms to `matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `matrix.to_bilin_form'`. -/
def BilinForm.toMatrixAux (b : n → M₂) : BilinForm R₂ M₂ →ₗ[R₂] Matrix n n R₂
    where
  toFun B := of fun i j => B (b i) (b j)
  map_add' f g := rfl
  map_smul' f g := rfl
#align bilin_form.to_matrix_aux BilinForm.toMatrixAux

@[simp]
theorem BilinForm.toMatrixAux_apply (B : BilinForm R₂ M₂) (b : n → M₂) (i j : n) :
    BilinForm.toMatrixAux b B i j = B (b i) (b j) :=
  rfl
#align bilin_form.to_matrix_aux_apply BilinForm.toMatrixAux_apply

variable [Fintype n] [Fintype o]

theorem toBilin'Aux_toMatrixAux [DecidableEq n] (B₂ : BilinForm R₂ (n → R₂)) :
    Matrix.toBilin'Aux (BilinForm.toMatrixAux (fun j => stdBasis R₂ (fun _ => R₂) j 1) B₂) = B₂ :=
  by
  refine' ext_basis (Pi.basisFun R₂ n) fun i j => _
  rw [Pi.basisFun_apply, Pi.basisFun_apply, Matrix.toBilin'Aux_stdBasis,
    BilinForm.toMatrixAux_apply]
#align to_bilin'_aux_to_matrix_aux toBilin'Aux_toMatrixAux

section ToMatrix'

/-! ### `to_matrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₂`.
-/


variable [DecidableEq n] [DecidableEq o]

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def BilinForm.toMatrix' : BilinForm R₂ (n → R₂) ≃ₗ[R₂] Matrix n n R₂ :=
  {
    BilinForm.toMatrixAux fun j =>
      stdBasis R₂ (fun _ => R₂) j
        1 with
    invFun := Matrix.toBilin'Aux
    left_inv := by convert toBilin'Aux_toMatrixAux
    right_inv := fun M => by
      ext (i j)
      simp only [to_fun_eq_coe, BilinForm.toMatrixAux_apply, Matrix.toBilin'Aux_stdBasis] }
#align bilin_form.to_matrix' BilinForm.toMatrix'

@[simp]
theorem BilinForm.toMatrixAux_stdBasis (B : BilinForm R₂ (n → R₂)) :
    BilinForm.toMatrixAux (fun j => stdBasis R₂ (fun _ => R₂) j 1) B = BilinForm.toMatrix' B :=
  rfl
#align bilin_form.to_matrix_aux_std_basis BilinForm.toMatrixAux_stdBasis

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def Matrix.toBilin' : Matrix n n R₂ ≃ₗ[R₂] BilinForm R₂ (n → R₂) :=
  BilinForm.toMatrix'.symm
#align matrix.to_bilin' Matrix.toBilin'

@[simp]
theorem Matrix.toBilin'Aux_eq (M : Matrix n n R₂) : Matrix.toBilin'Aux M = Matrix.toBilin' M :=
  rfl
#align matrix.to_bilin'_aux_eq Matrix.toBilin'Aux_eq

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
theorem Matrix.toBilin'_apply (M : Matrix n n R₂) (x y : n → R₂) :
    Matrix.toBilin' M x y = ∑ (i) (j), x i * M i j * y j :=
  rfl
#align matrix.to_bilin'_apply Matrix.toBilin'_apply

theorem Matrix.toBilin'_apply' (M : Matrix n n R₂) (v w : n → R₂) :
    Matrix.toBilin' M v w = Matrix.dotProduct v (M.mulVec w) :=
  by
  simp_rw [Matrix.toBilin'_apply, Matrix.dotProduct, Matrix.mulVec, Matrix.dotProduct]
  refine' Finset.sum_congr rfl fun _ _ => _
  rw [Finset.mul_sum]
  refine' Finset.sum_congr rfl fun _ _ => _
  rw [← mul_assoc]
#align matrix.to_bilin'_apply' Matrix.toBilin'_apply'

@[simp]
theorem Matrix.toBilin'_stdBasis (M : Matrix n n R₂) (i j : n) :
    Matrix.toBilin' M (stdBasis R₂ (fun _ => R₂) i 1) (stdBasis R₂ (fun _ => R₂) j 1) = M i j :=
  Matrix.toBilin'Aux_stdBasis M i j
#align matrix.to_bilin'_std_basis Matrix.toBilin'_stdBasis

@[simp]
theorem BilinForm.toMatrix'_symm :
    (BilinForm.toMatrix'.symm : Matrix n n R₂ ≃ₗ[R₂] _) = Matrix.toBilin' :=
  rfl
#align bilin_form.to_matrix'_symm BilinForm.toMatrix'_symm

@[simp]
theorem Matrix.toBilin'_symm :
    (Matrix.toBilin'.symm : _ ≃ₗ[R₂] Matrix n n R₂) = BilinForm.toMatrix' :=
  BilinForm.toMatrix'.symm_symm
#align matrix.to_bilin'_symm Matrix.toBilin'_symm

@[simp]
theorem Matrix.toBilin'_toMatrix' (B : BilinForm R₂ (n → R₂)) :
    Matrix.toBilin' (BilinForm.toMatrix' B) = B :=
  Matrix.toBilin'.apply_symm_apply B
#align matrix.to_bilin'_to_matrix' Matrix.toBilin'_toMatrix'

@[simp]
theorem BilinForm.toMatrix'_toBilin' (M : Matrix n n R₂) :
    BilinForm.toMatrix' (Matrix.toBilin' M) = M :=
  BilinForm.toMatrix'.apply_symm_apply M
#align bilin_form.to_matrix'_to_bilin' BilinForm.toMatrix'_toBilin'

@[simp]
theorem BilinForm.toMatrix'_apply (B : BilinForm R₂ (n → R₂)) (i j : n) :
    BilinForm.toMatrix' B i j = B (stdBasis R₂ (fun _ => R₂) i 1) (stdBasis R₂ (fun _ => R₂) j 1) :=
  rfl
#align bilin_form.to_matrix'_apply BilinForm.toMatrix'_apply

@[simp]
theorem BilinForm.toMatrix'_comp (B : BilinForm R₂ (n → R₂)) (l r : (o → R₂) →ₗ[R₂] n → R₂) :
    (B.comp l r).toMatrix' = l.toMatrix'ᵀ ⬝ B.toMatrix' ⬝ r.toMatrix' :=
  by
  ext (i j)
  simp only [BilinForm.toMatrix'_apply, BilinForm.comp_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix', LinearEquiv.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← BilinForm.sum_repr_mul_repr_mul (Pi.basisFun R₂ n) (l _) (r _)]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, Pi.basisFun_repr, mul_assoc, mul_comm, mul_left_comm,
        Pi.basisFun_apply, of_apply]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp only [zero_smul, Finsupp.sum_zero]
#align bilin_form.to_matrix'_comp BilinForm.toMatrix'_comp

theorem BilinForm.toMatrix'_compLeft (B : BilinForm R₂ (n → R₂)) (f : (n → R₂) →ₗ[R₂] n → R₂) :
    (B.compLeft f).toMatrix' = f.toMatrix'ᵀ ⬝ B.toMatrix' := by
  simp only [BilinForm.compLeft, BilinForm.toMatrix'_comp, to_matrix'_id, Matrix.mul_one]
#align bilin_form.to_matrix'_comp_left BilinForm.toMatrix'_compLeft

theorem BilinForm.toMatrix'_compRight (B : BilinForm R₂ (n → R₂)) (f : (n → R₂) →ₗ[R₂] n → R₂) :
    (B.compRight f).toMatrix' = B.toMatrix' ⬝ f.toMatrix' := by
  simp only [BilinForm.compRight, BilinForm.toMatrix'_comp, to_matrix'_id, transpose_one,
    Matrix.one_mul]
#align bilin_form.to_matrix'_comp_right BilinForm.toMatrix'_compRight

theorem BilinForm.mul_toMatrix'_mul (B : BilinForm R₂ (n → R₂)) (M : Matrix o n R₂)
    (N : Matrix n o R₂) : M ⬝ B.toMatrix' ⬝ N = (B.comp Mᵀ.toLin' N.toLin').toMatrix' := by
  simp only [B.to_matrix'_comp, transpose_transpose, to_matrix'_to_lin']
#align bilin_form.mul_to_matrix'_mul BilinForm.mul_toMatrix'_mul

theorem BilinForm.mul_toMatrix' (B : BilinForm R₂ (n → R₂)) (M : Matrix n n R₂) :
    M ⬝ B.toMatrix' = (B.compLeft Mᵀ.toLin').toMatrix' := by
  simp only [B.to_matrix'_comp_left, transpose_transpose, to_matrix'_to_lin']
#align bilin_form.mul_to_matrix' BilinForm.mul_toMatrix'

theorem BilinForm.toMatrix'_mul (B : BilinForm R₂ (n → R₂)) (M : Matrix n n R₂) :
    B.toMatrix' ⬝ M = (B.compRight M.toLin').toMatrix' := by
  simp only [B.to_matrix'_comp_right, to_matrix'_to_lin']
#align bilin_form.to_matrix'_mul BilinForm.toMatrix'_mul

theorem Matrix.toBilin'_comp (M : Matrix n n R₂) (P Q : Matrix n o R₂) :
    M.toBilin'.comp P.toLin' Q.toLin' = (Pᵀ ⬝ M ⬝ Q).toBilin' :=
  BilinForm.toMatrix'.Injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', to_matrix'_to_lin'])
#align matrix.to_bilin'_comp Matrix.toBilin'_comp

end ToMatrix'

section ToMatrix

/-! ### `to_matrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/


variable [DecidableEq n] (b : Basis n R₂ M₂)

/-- `bilin_form.to_matrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def BilinForm.toMatrix : BilinForm R₂ M₂ ≃ₗ[R₂] Matrix n n R₂ :=
  (BilinForm.congr b.equivFun).trans BilinForm.toMatrix'
#align bilin_form.to_matrix BilinForm.toMatrix

/-- `bilin_form.to_matrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def Matrix.toBilin : Matrix n n R₂ ≃ₗ[R₂] BilinForm R₂ M₂ :=
  (BilinForm.toMatrix b).symm
#align matrix.to_bilin Matrix.toBilin

@[simp]
theorem BilinForm.toMatrix_apply (B : BilinForm R₂ M₂) (i j : n) :
    BilinForm.toMatrix b B i j = B (b i) (b j) := by
  rw [BilinForm.toMatrix, LinearEquiv.trans_apply, BilinForm.toMatrix'_apply, congr_apply,
    b.equiv_fun_symm_std_basis, b.equiv_fun_symm_std_basis]
#align bilin_form.to_matrix_apply BilinForm.toMatrix_apply

/- ./././Mathport/Syntax/Translate/Expr.lean:107:6: warning: expanding binder group (i j) -/
@[simp]
theorem Matrix.toBilin_apply (M : Matrix n n R₂) (x y : M₂) :
    Matrix.toBilin b M x y = ∑ (i) (j), b.repr x i * M i j * b.repr y j :=
  by
  rw [Matrix.toBilin, BilinForm.toMatrix, LinearEquiv.symm_trans_apply, ← Matrix.toBilin']
  simp only [congr_symm, congr_apply, LinearEquiv.symm_symm, Matrix.toBilin'_apply,
    Basis.equivFun_apply]
#align matrix.to_bilin_apply Matrix.toBilin_apply

-- Not a `simp` lemma since `bilin_form.to_matrix` needs an extra argument
theorem BilinearForm.toMatrixAux_eq (B : BilinForm R₂ M₂) :
    BilinForm.toMatrixAux b B = BilinForm.toMatrix b B :=
  ext fun i j => by rw [BilinForm.toMatrix_apply, BilinForm.toMatrixAux_apply]
#align bilinear_form.to_matrix_aux_eq BilinearForm.toMatrixAux_eq

@[simp]
theorem BilinForm.toMatrix_symm : (BilinForm.toMatrix b).symm = Matrix.toBilin b :=
  rfl
#align bilin_form.to_matrix_symm BilinForm.toMatrix_symm

@[simp]
theorem Matrix.toBilin_symm : (Matrix.toBilin b).symm = BilinForm.toMatrix b :=
  (BilinForm.toMatrix b).symm_symm
#align matrix.to_bilin_symm Matrix.toBilin_symm

theorem Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₂ n) = Matrix.toBilin' :=
  by
  ext M
  simp only [Matrix.toBilin_apply, Matrix.toBilin'_apply, Pi.basisFun_repr]
#align matrix.to_bilin_basis_fun Matrix.toBilin_basisFun

theorem BilinForm.toMatrix_basisFun : BilinForm.toMatrix (Pi.basisFun R₂ n) = BilinForm.toMatrix' :=
  by
  ext B
  rw [BilinForm.toMatrix_apply, BilinForm.toMatrix'_apply, Pi.basisFun_apply, Pi.basisFun_apply]
#align bilin_form.to_matrix_basis_fun BilinForm.toMatrix_basisFun

@[simp]
theorem Matrix.toBilin_toMatrix (B : BilinForm R₂ M₂) :
    Matrix.toBilin b (BilinForm.toMatrix b B) = B :=
  (Matrix.toBilin b).apply_symm_apply B
#align matrix.to_bilin_to_matrix Matrix.toBilin_toMatrix

@[simp]
theorem BilinForm.toMatrix_toBilin (M : Matrix n n R₂) :
    BilinForm.toMatrix b (Matrix.toBilin b M) = M :=
  (BilinForm.toMatrix b).apply_symm_apply M
#align bilin_form.to_matrix_to_bilin BilinForm.toMatrix_toBilin

variable {M₂' : Type _} [AddCommMonoid M₂'] [Module R₂ M₂']

variable (c : Basis o R₂ M₂')

variable [DecidableEq o]

-- Cannot be a `simp` lemma because `b` must be inferred.
theorem BilinForm.toMatrix_comp (B : BilinForm R₂ M₂) (l r : M₂' →ₗ[R₂] M₂) :
    BilinForm.toMatrix c (B.comp l r) =
      (toMatrix c b l)ᵀ ⬝ BilinForm.toMatrix b B ⬝ toMatrix c b r :=
  by
  ext (i j)
  simp only [BilinForm.toMatrix_apply, BilinForm.comp_apply, transpose_apply, Matrix.mul_apply,
    LinearMap.toMatrix', LinearEquiv.coe_mk, sum_mul]
  rw [sum_comm]
  conv_lhs => rw [← BilinForm.sum_repr_mul_repr_mul b]
  rw [Finsupp.sum_fintype]
  · apply sum_congr rfl
    rintro i' -
    rw [Finsupp.sum_fintype]
    · apply sum_congr rfl
      rintro j' -
      simp only [smul_eq_mul, LinearMap.toMatrix_apply, Basis.equivFun_apply, mul_assoc, mul_comm,
        mul_left_comm]
    · intros
      simp only [zero_smul, smul_zero]
  · intros
    simp only [zero_smul, Finsupp.sum_zero]
#align bilin_form.to_matrix_comp BilinForm.toMatrix_comp

theorem BilinForm.toMatrix_compLeft (B : BilinForm R₂ M₂) (f : M₂ →ₗ[R₂] M₂) :
    BilinForm.toMatrix b (B.compLeft f) = (toMatrix b b f)ᵀ ⬝ BilinForm.toMatrix b B := by
  simp only [comp_left, BilinForm.toMatrix_comp b b, to_matrix_id, Matrix.mul_one]
#align bilin_form.to_matrix_comp_left BilinForm.toMatrix_compLeft

theorem BilinForm.toMatrix_compRight (B : BilinForm R₂ M₂) (f : M₂ →ₗ[R₂] M₂) :
    BilinForm.toMatrix b (B.compRight f) = BilinForm.toMatrix b B ⬝ toMatrix b b f := by
  simp only [BilinForm.compRight, BilinForm.toMatrix_comp b b, to_matrix_id, transpose_one,
    Matrix.one_mul]
#align bilin_form.to_matrix_comp_right BilinForm.toMatrix_compRight

@[simp]
theorem BilinForm.toMatrix_mul_basis_toMatrix (c : Basis o R₂ M₂) (B : BilinForm R₂ M₂) :
    (b.toMatrix c)ᵀ ⬝ BilinForm.toMatrix b B ⬝ b.toMatrix c = BilinForm.toMatrix c B := by
  rw [← LinearMap.toMatrix_id_eq_basis_toMatrix, ← BilinForm.toMatrix_comp, BilinForm.comp_id_id]
#align bilin_form.to_matrix_mul_basis_to_matrix BilinForm.toMatrix_mul_basis_toMatrix

theorem BilinForm.mul_toMatrix_mul (B : BilinForm R₂ M₂) (M : Matrix o n R₂) (N : Matrix n o R₂) :
    M ⬝ BilinForm.toMatrix b B ⬝ N = BilinForm.toMatrix c (B.comp (toLin c b Mᵀ) (toLin c b N)) :=
  by simp only [B.to_matrix_comp b c, to_matrix_to_lin, transpose_transpose]
#align bilin_form.mul_to_matrix_mul BilinForm.mul_toMatrix_mul

theorem BilinForm.mul_toMatrix (B : BilinForm R₂ M₂) (M : Matrix n n R₂) :
    M ⬝ BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (toLin b b Mᵀ)) := by
  rw [B.to_matrix_comp_left b, to_matrix_to_lin, transpose_transpose]
#align bilin_form.mul_to_matrix BilinForm.mul_toMatrix

theorem BilinForm.toMatrix_mul (B : BilinForm R₂ M₂) (M : Matrix n n R₂) :
    BilinForm.toMatrix b B ⬝ M = BilinForm.toMatrix b (B.compRight (toLin b b M)) := by
  rw [B.to_matrix_comp_right b, to_matrix_to_lin]
#align bilin_form.to_matrix_mul BilinForm.toMatrix_mul

theorem Matrix.toBilin_comp (M : Matrix n n R₂) (P Q : Matrix n o R₂) :
    (Matrix.toBilin b M).comp (toLin c b P) (toLin c b Q) = Matrix.toBilin c (Pᵀ ⬝ M ⬝ Q) :=
  (BilinForm.toMatrix c).Injective
    (by simp only [BilinForm.toMatrix_comp b c, BilinForm.toMatrix_toBilin, to_matrix_to_lin])
#align matrix.to_bilin_comp Matrix.toBilin_comp

end ToMatrix

end Matrix

section MatrixAdjoints

open Matrix

variable {n : Type _} [Fintype n]

variable (b : Basis n R₃ M₃)

variable (J J₃ A A' : Matrix n n R₃)

@[simp]
theorem isAdjointPair_toBilin' [DecidableEq n] :
    BilinForm.IsAdjointPair (Matrix.toBilin' J) (Matrix.toBilin' J₃) (Matrix.toLin' A)
        (Matrix.toLin' A') ↔
      Matrix.IsAdjointPair J J₃ A A' :=
  by
  rw [BilinForm.isAdjointPair_iff_compLeft_eq_compRight]
  have h :
    ∀ B B' : BilinForm R₃ (n → R₃), B = B' ↔ BilinForm.toMatrix' B = BilinForm.toMatrix' B' :=
    by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact bilin_form.to_matrix'.injective h
  rw [h, BilinForm.toMatrix'_compLeft, BilinForm.toMatrix'_compRight, LinearMap.toMatrix'_toLin',
    LinearMap.toMatrix'_toLin', BilinForm.toMatrix'_toBilin', BilinForm.toMatrix'_toBilin']
  rfl
#align is_adjoint_pair_to_bilin' isAdjointPair_toBilin'

@[simp]
theorem isAdjointPair_toBilin [DecidableEq n] :
    BilinForm.IsAdjointPair (Matrix.toBilin b J) (Matrix.toBilin b J₃) (Matrix.toLin b b A)
        (Matrix.toLin b b A') ↔
      Matrix.IsAdjointPair J J₃ A A' :=
  by
  rw [BilinForm.isAdjointPair_iff_compLeft_eq_compRight]
  have h : ∀ B B' : BilinForm R₃ M₃, B = B' ↔ BilinForm.toMatrix b B = BilinForm.toMatrix b B' :=
    by
    intro B B'
    constructor <;> intro h
    · rw [h]
    · exact (BilinForm.toMatrix b).Injective h
  rw [h, BilinForm.toMatrix_compLeft, BilinForm.toMatrix_compRight, LinearMap.toMatrix_toLin,
    LinearMap.toMatrix_toLin, BilinForm.toMatrix_toBilin, BilinForm.toMatrix_toBilin]
  rfl
#align is_adjoint_pair_to_bilin isAdjointPair_toBilin

theorem Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₃) (h : IsUnit P) :
    (Pᵀ ⬝ J ⬝ P).IsAdjointPair (Pᵀ ⬝ J ⬝ P) A A' ↔ J.IsAdjointPair J (P ⬝ A ⬝ P⁻¹) (P ⬝ A' ⬝ P⁻¹) :=
  by
  have h' : IsUnit P.det := P.isUnit_iff_isUnit_det.mp h
  let u := P.nonsing_inv_unit h'
  let v := Pᵀ.nonsingInvUnit (P.is_unit_det_transpose h')
  let x := Aᵀ * Pᵀ * J
  let y := J * P * A'
  suffices x * ↑u = ↑v * y ↔ ↑v⁻¹ * x = y * ↑u⁻¹
    by
    dsimp only [Matrix.IsAdjointPair]
    repeat' rw [Matrix.transpose_mul]
    simp only [← Matrix.mul_eq_mul, ← mul_assoc, P.transpose_nonsing_inv]
    conv_lhs =>
      rhs
      rw [mul_assoc, mul_assoc]
      congr
      skip
      rw [← mul_assoc]
    conv_rhs =>
      rw [mul_assoc, mul_assoc]
      conv =>
        lhs
        congr
        skip
        rw [← mul_assoc]
    exact this
  rw [Units.eq_mul_inv_iff_mul_eq]
  conv_rhs => rw [mul_assoc]
  rw [v.inv_mul_eq_iff_eq_mul]
#align matrix.is_adjoint_pair_equiv' Matrix.isAdjointPair_equiv'

variable [DecidableEq n]

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pairSelfAdjointMatricesSubmodule' : Submodule R₃ (Matrix n n R₃) :=
  (BilinForm.isPairSelfAdjointSubmodule (Matrix.toBilin' J) (Matrix.toBilin' J₃)).map
    ((LinearMap.toMatrix' : ((n → R₃) →ₗ[R₃] n → R₃) ≃ₗ[R₃] Matrix n n R₃) :
      ((n → R₃) →ₗ[R₃] n → R₃) →ₗ[R₃] Matrix n n R₃)
#align pair_self_adjoint_matrices_submodule' pairSelfAdjointMatricesSubmodule'

theorem mem_pair_self_adjoint_matrices_submodule' :
    A ∈ pairSelfAdjointMatricesSubmodule J J₃ ↔ Matrix.IsAdjointPair J J₃ A A := by
  simp only [mem_pairSelfAdjointMatricesSubmodule]
#align mem_pair_self_adjoint_matrices_submodule' mem_pair_self_adjoint_matrices_submodule'

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def selfAdjointMatricesSubmodule' : Submodule R₃ (Matrix n n R₃) :=
  pairSelfAdjointMatricesSubmodule J J
#align self_adjoint_matrices_submodule' selfAdjointMatricesSubmodule'

theorem mem_self_adjoint_matrices_submodule' :
    A ∈ selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A := by
  simp only [mem_selfAdjointMatricesSubmodule]
#align mem_self_adjoint_matrices_submodule' mem_self_adjoint_matrices_submodule'

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skewAdjointMatricesSubmodule' : Submodule R₃ (Matrix n n R₃) :=
  pairSelfAdjointMatricesSubmodule (-J) J
#align skew_adjoint_matrices_submodule' skewAdjointMatricesSubmodule'

theorem mem_skew_adjoint_matrices_submodule' :
    A ∈ skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A := by
  simp only [mem_skewAdjointMatricesSubmodule]
#align mem_skew_adjoint_matrices_submodule' mem_skew_adjoint_matrices_submodule'

end MatrixAdjoints

namespace BilinForm

section Det

open Matrix

variable {A : Type _} [CommRing A] [IsDomain A] [Module A M₃] (B₃ : BilinForm A M₃)

variable {ι : Type _} [DecidableEq ι] [Fintype ι]

theorem Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin {M : Matrix ι ι R₂}
    (b : Basis ι R₂ M₂) : M.toBilin'.Nondegenerate ↔ (Matrix.toBilin b M).Nondegenerate :=
  (nondegenerate_congr_iff b.equivFun.symm).symm
#align matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form
theorem Matrix.Nondegenerate.toBilin' {M : Matrix ι ι R₃} (h : M.Nondegenerate) :
    M.toBilin'.Nondegenerate := fun x hx =>
  h.eq_zero_of_ortho fun y => by simpa only [to_bilin'_apply'] using hx y
#align matrix.nondegenerate.to_bilin' Matrix.Nondegenerate.toBilin'

@[simp]
theorem Matrix.nondegenerate_toBilin'_iff {M : Matrix ι ι R₃} :
    M.toBilin'.Nondegenerate ↔ M.Nondegenerate :=
  ⟨fun h v hv => h v fun w => (M.toBilin'_apply' _ _).trans <| hv w, Matrix.Nondegenerate.toBilin'⟩
#align matrix.nondegenerate_to_bilin'_iff Matrix.nondegenerate_toBilin'_iff

theorem Matrix.Nondegenerate.toBilin {M : Matrix ι ι R₃} (h : M.Nondegenerate) (b : Basis ι R₃ M₃) :
    (toBilin b M).Nondegenerate :=
  (Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin b).mp h.toBilin'
#align matrix.nondegenerate.to_bilin Matrix.Nondegenerate.toBilin

@[simp]
theorem Matrix.nondegenerate_toBilin_iff {M : Matrix ι ι R₃} (b : Basis ι R₃ M₃) :
    (toBilin b M).Nondegenerate ↔ M.Nondegenerate := by
  rw [← Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin, Matrix.nondegenerate_toBilin'_iff]
#align matrix.nondegenerate_to_bilin_iff Matrix.nondegenerate_toBilin_iff

-- Lemmas transferring nondegeneracy between a bilinear form and its associated matrix
@[simp]
theorem nondegenerate_toMatrix'_iff {B : BilinForm R₃ (ι → R₃)} :
    B.toMatrix'.Nondegenerate ↔ B.Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.symm.trans <| (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl
#align bilin_form.nondegenerate_to_matrix'_iff BilinForm.nondegenerate_toMatrix'_iff

theorem Nondegenerate.toMatrix' {B : BilinForm R₃ (ι → R₃)} (h : B.Nondegenerate) :
    B.toMatrix'.Nondegenerate :=
  nondegenerate_toMatrix'_iff.mpr h
#align bilin_form.nondegenerate.to_matrix' BilinForm.Nondegenerate.toMatrix'

@[simp]
theorem nondegenerate_toMatrix_iff {B : BilinForm R₃ M₃} (b : Basis ι R₃ M₃) :
    (toMatrix b B).Nondegenerate ↔ B.Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff b).symm.trans <| (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl
#align bilin_form.nondegenerate_to_matrix_iff BilinForm.nondegenerate_toMatrix_iff

theorem Nondegenerate.toMatrix {B : BilinForm R₃ M₃} (h : B.Nondegenerate) (b : Basis ι R₃ M₃) :
    (toMatrix b B).Nondegenerate :=
  (nondegenerate_toMatrix_iff b).mpr h
#align bilin_form.nondegenerate.to_matrix BilinForm.Nondegenerate.toMatrix

-- Some shorthands for combining the above with `matrix.nondegenerate_of_det_ne_zero`
theorem nondegenerate_toBilin'_iff_det_ne_zero {M : Matrix ι ι A} :
    M.toBilin'.Nondegenerate ↔ M.det ≠ 0 := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]
#align bilin_form.nondegenerate_to_bilin'_iff_det_ne_zero BilinForm.nondegenerate_toBilin'_iff_det_ne_zero

theorem nondegenerate_toBilin'_of_det_ne_zero' (M : Matrix ι ι A) (h : M.det ≠ 0) :
    M.toBilin'.Nondegenerate :=
  nondegenerate_toBilin'_iff_det_ne_zero.mpr h
#align bilin_form.nondegenerate_to_bilin'_of_det_ne_zero' BilinForm.nondegenerate_toBilin'_of_det_ne_zero'

theorem nondegenerate_iff_det_ne_zero {B : BilinForm A M₃} (b : Basis ι A M₃) :
    B.Nondegenerate ↔ (toMatrix b B).det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_to_matrix_iff]
#align bilin_form.nondegenerate_iff_det_ne_zero BilinForm.nondegenerate_iff_det_ne_zero

theorem nondegenerate_of_det_ne_zero (b : Basis ι A M₃) (h : (toMatrix b B₃).det ≠ 0) :
    B₃.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero b).mpr h
#align bilin_form.nondegenerate_of_det_ne_zero BilinForm.nondegenerate_of_det_ne_zero

end Det

end BilinForm


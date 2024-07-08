/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying
-/
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

#align_import linear_algebra.matrix.bilinear_form from "leanprover-community/mathlib"@"075b3f7d19b9da85a0b54b3e33055a74fc388dec"

/-!
# Bilinear form

This file defines the conversion between bilinear forms and matrices.

## Main definitions

 * `Matrix.toBilin` given a basis define a bilinear form
 * `Matrix.toBilin'` define the bilinear form on `n → R`
 * `BilinForm.toMatrix`: calculate the matrix coefficients of a bilinear form
 * `BilinForm.toMatrix'`: calculate the matrix coefficients of a bilinear form on `n → R`

## Notations

In this file we use the following type variables:
 - `M`, `M'`, ... are modules over the commutative semiring `R`,
 - `M₁`, `M₁'`, ... are modules over the commutative ring `R₁`,
 - `M₂`, `M₂'`, ... are modules over the commutative semiring `R₂`,
 - `M₃`, `M₃'`, ... are modules over the commutative ring `R₃`,
 - `V`, ... is a vector space over the field `K`.

## Tags

bilinear form, bilin form, BilinearForm, matrix, basis

-/

open LinearMap (BilinForm)

variable {R : Type*} {M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
variable {R₁ : Type*} {M₁ : Type*} [CommRing R₁] [AddCommGroup M₁] [Module R₁ M₁]
variable {R₂ : Type*} {M₂ : Type*} [CommSemiring R₂] [AddCommMonoid M₂] [Module R₂ M₂]
variable {R₃ : Type*} {M₃ : Type*} [CommRing R₃] [AddCommGroup M₃] [Module R₃ M₃]
variable {V : Type*} {K : Type*} [Field K] [AddCommGroup V] [Module K V]
variable {B : BilinForm R M} {B₁ : BilinForm R₁ M₁} {B₂ : BilinForm R₂ M₂}

section Matrix

variable {n o : Type*}

open Finset LinearMap Matrix

open Matrix

/-- The map from `Matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
def Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₂) : BilinForm R₂ (n → R₂) :=
  Matrix.toLinearMap₂'Aux _ _ M
#align matrix.to_bilin'_aux Matrix.toBilin'Aux

theorem Matrix.toBilin'Aux_stdBasis [Fintype n] [DecidableEq n] (M : Matrix n n R₂) (i j : n) :
    M.toBilin'Aux (LinearMap.stdBasis R₂ (fun _ => R₂) i 1)
      (LinearMap.stdBasis R₂ (fun _ => R₂) j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_stdBasis _ _ _ _ _
#align matrix.to_bilin'_aux_std_basis Matrix.toBilin'Aux_stdBasis

/-- The linear map from bilinear forms to `Matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
def BilinForm.toMatrixAux (b : n → M₂) : BilinForm R₂ M₂ →ₗ[R₂] Matrix n n R₂ :=
  LinearMap.toMatrix₂Aux b b
#align bilin_form.to_matrix_aux BilinForm.toMatrixAux

@[simp]
theorem LinearMap.BilinForm.toMatrixAux_apply (B : BilinForm R₂ M₂) (b : n → M₂) (i j : n) :
    -- Porting note: had to hint the base ring even though it should be clear from context...
    BilinForm.toMatrixAux (R₂ := R₂) b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂Aux_apply B _ _ _ _
#align bilin_form.to_matrix_aux_apply LinearMap.BilinForm.toMatrixAux_apply

variable [Fintype n] [Fintype o]

theorem toBilin'Aux_toMatrixAux [DecidableEq n] (B₂ : BilinForm R₂ (n → R₂)) :
    -- Porting note: had to hint the base ring even though it should be clear from context...
    Matrix.toBilin'Aux (BilinForm.toMatrixAux (R₂ := R₂)
      (fun j => stdBasis R₂ (fun _ => R₂) j 1) B₂) = B₂ := by
  rw [BilinForm.toMatrixAux, Matrix.toBilin'Aux,
    toLinearMap₂'Aux_toMatrix₂Aux]
#align to_bilin'_aux_to_matrix_aux toBilin'Aux_toMatrixAux

section ToMatrix'

/-! ### `ToMatrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₂`.
-/


variable [DecidableEq n] [DecidableEq o]

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def LinearMap.BilinForm.toMatrix' : BilinForm R₂ (n → R₂) ≃ₗ[R₂] Matrix n n R₂ :=
  LinearMap.toMatrix₂'
#align bilin_form.to_matrix' LinearMap.BilinForm.toMatrix'

@[simp]
theorem LinearMap.BilinForm.toMatrixAux_stdBasis (B : BilinForm R₂ (n → R₂)) :
    -- Porting note: had to hint the base ring even though it should be clear from context...
    BilinForm.toMatrixAux (R₂ := R₂) (fun j => stdBasis R₂ (fun _ => R₂) j 1) B =
      BilinForm.toMatrix' B :=
  rfl
#align bilin_form.to_matrix_aux_std_basis LinearMap.BilinForm.toMatrixAux_stdBasis

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def Matrix.toBilin' : Matrix n n R₂ ≃ₗ[R₂] BilinForm R₂ (n → R₂) :=
  BilinForm.toMatrix'.symm
#align matrix.to_bilin' Matrix.toBilin'

@[simp]
theorem Matrix.toBilin'Aux_eq (M : Matrix n n R₂) : Matrix.toBilin'Aux M = Matrix.toBilin' M :=
  rfl
#align matrix.to_bilin'_aux_eq Matrix.toBilin'Aux_eq

theorem Matrix.toBilin'_apply (M : Matrix n n R₂) (x y : n → R₂) :
    Matrix.toBilin' M x y = ∑ i, ∑ j, x i * M i j * y j := Matrix.toLinearMap₂'_apply _ _ _
#align matrix.to_bilin'_apply Matrix.toBilin'_apply

theorem Matrix.toBilin'_apply' (M : Matrix n n R₂) (v w : n → R₂) :
    Matrix.toBilin' M v w = Matrix.dotProduct v (M *ᵥ w) := Matrix.toLinearMap₂'_apply' _ _ _
#align matrix.to_bilin'_apply' Matrix.toBilin'_apply'

@[simp]
theorem Matrix.toBilin'_stdBasis (M : Matrix n n R₂) (i j : n) :
    Matrix.toBilin' M
      (LinearMap.stdBasis R₂ (fun _ => R₂) i 1)
      (LinearMap.stdBasis R₂ (fun _ => R₂) j 1) = M i j := Matrix.toLinearMap₂'_stdBasis _ _ _
#align matrix.to_bilin'_std_basis Matrix.toBilin'_stdBasis

@[simp]
theorem LinearMap.BilinForm.toMatrix'_symm :
    (BilinForm.toMatrix'.symm : Matrix n n R₂ ≃ₗ[R₂] _) = Matrix.toBilin' :=
  rfl
#align bilin_form.to_matrix'_symm LinearMap.BilinForm.toMatrix'_symm

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

namespace LinearMap

@[simp]
theorem BilinForm.toMatrix'_toBilin' (M : Matrix n n R₂) :
    BilinForm.toMatrix' (Matrix.toBilin' M) = M :=
  LinearMap.toMatrix₂'.apply_symm_apply M
#align bilin_form.to_matrix'_to_bilin' LinearMap.BilinForm.toMatrix'_toBilin'

@[simp]
theorem BilinForm.toMatrix'_apply (B : BilinForm R₂ (n → R₂)) (i j : n) :
    BilinForm.toMatrix' B i j = B (stdBasis R₂ (fun _ => R₂) i 1) (stdBasis R₂ (fun _ => R₂) j 1) :=
  LinearMap.toMatrix₂'_apply _ _ _
#align bilin_form.to_matrix'_apply LinearMap.BilinForm.toMatrix'_apply

-- Porting note: dot notation for bundled maps doesn't work in the rest of this section
@[simp]
theorem BilinForm.toMatrix'_comp (B : BilinForm R₂ (n → R₂)) (l r : (o → R₂) →ₗ[R₂] n → R₂) :
    BilinForm.toMatrix' (B.comp l r) =
      (LinearMap.toMatrix' l)ᵀ * BilinForm.toMatrix' B * LinearMap.toMatrix' r :=
  LinearMap.toMatrix₂'_compl₁₂ B _ _
#align bilin_form.to_matrix'_comp LinearMap.BilinForm.toMatrix'_comp

theorem BilinForm.toMatrix'_compLeft (B : BilinForm R₂ (n → R₂)) (f : (n → R₂) →ₗ[R₂] n → R₂) :
    BilinForm.toMatrix' (B.compLeft f) = (LinearMap.toMatrix' f)ᵀ * BilinForm.toMatrix' B :=
  LinearMap.toMatrix₂'_comp B _
#align bilin_form.to_matrix'_comp_left LinearMap.BilinForm.toMatrix'_compLeft

theorem BilinForm.toMatrix'_compRight (B : BilinForm R₂ (n → R₂)) (f : (n → R₂) →ₗ[R₂] n → R₂) :
    BilinForm.toMatrix' (B.compRight f) = BilinForm.toMatrix' B * LinearMap.toMatrix' f :=
  LinearMap.toMatrix₂'_compl₂ B _
#align bilin_form.to_matrix'_comp_right LinearMap.BilinForm.toMatrix'_compRight

theorem BilinForm.mul_toMatrix'_mul (B : BilinForm R₂ (n → R₂)) (M : Matrix o n R₂)
    (N : Matrix n o R₂) : M * BilinForm.toMatrix' B * N =
      BilinForm.toMatrix' (B.comp (Matrix.toLin' Mᵀ) (Matrix.toLin' N)) :=
  LinearMap.mul_toMatrix₂'_mul B _ _
#align bilin_form.mul_to_matrix'_mul LinearMap.BilinForm.mul_toMatrix'_mul

theorem BilinForm.mul_toMatrix' (B : BilinForm R₂ (n → R₂)) (M : Matrix n n R₂) :
    M * BilinForm.toMatrix' B = BilinForm.toMatrix' (B.compLeft (Matrix.toLin' Mᵀ)) :=
  LinearMap.mul_toMatrix' B _
#align bilin_form.mul_to_matrix' LinearMap.BilinForm.mul_toMatrix'

theorem BilinForm.toMatrix'_mul (B : BilinForm R₂ (n → R₂)) (M : Matrix n n R₂) :
    BilinForm.toMatrix' B * M = BilinForm.toMatrix' (B.compRight (Matrix.toLin' M)) :=
  LinearMap.toMatrix₂'_mul B _
#align bilin_form.to_matrix'_mul LinearMap.BilinForm.toMatrix'_mul

end LinearMap

theorem Matrix.toBilin'_comp (M : Matrix n n R₂) (P Q : Matrix n o R₂) :
    M.toBilin'.comp (Matrix.toLin' P) (Matrix.toLin' Q) = Matrix.toBilin' (Pᵀ * M * Q) :=
  BilinForm.toMatrix'.injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])
#align matrix.to_bilin'_comp Matrix.toBilin'_comp

end ToMatrix'

section ToMatrix

/-! ### `ToMatrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/


variable [DecidableEq n] (b : Basis n R₂ M₂)

/-- `BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def BilinForm.toMatrix : BilinForm R₂ M₂ ≃ₗ[R₂] Matrix n n R₂ :=
  LinearMap.toMatrix₂ b b
#align bilin_form.to_matrix BilinForm.toMatrix

/-- `BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def Matrix.toBilin : Matrix n n R₂ ≃ₗ[R₂] BilinForm R₂ M₂ :=
  (BilinForm.toMatrix b).symm
#align matrix.to_bilin Matrix.toBilin

@[simp]
theorem BilinForm.toMatrix_apply (B : BilinForm R₂ M₂) (i j : n) :
    BilinForm.toMatrix b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂_apply _ _ B _ _
#align bilin_form.to_matrix_apply BilinForm.toMatrix_apply

@[simp]
theorem Matrix.toBilin_apply (M : Matrix n n R₂) (x y : M₂) :
    Matrix.toBilin b M x y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j :=
  Matrix.toLinearMap₂_apply _ _ _ _ _
#align matrix.to_bilin_apply Matrix.toBilin_apply

-- Not a `simp` lemma since `BilinForm.toMatrix` needs an extra argument
theorem BilinearForm.toMatrixAux_eq (B : BilinForm R₂ M₂) :
    BilinForm.toMatrixAux (R₂ := R₂) b B = BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂Aux_eq _ _ B
#align bilinear_form.to_matrix_aux_eq BilinearForm.toMatrixAux_eq

@[simp]
theorem BilinForm.toMatrix_symm : (BilinForm.toMatrix b).symm = Matrix.toBilin b :=
  rfl
#align bilin_form.to_matrix_symm BilinForm.toMatrix_symm

@[simp]
theorem Matrix.toBilin_symm : (Matrix.toBilin b).symm = BilinForm.toMatrix b :=
  (BilinForm.toMatrix b).symm_symm
#align matrix.to_bilin_symm Matrix.toBilin_symm

theorem Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₂ n) = Matrix.toBilin' := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]
#align matrix.to_bilin_basis_fun Matrix.toBilin_basisFun

theorem BilinForm.toMatrix_basisFun :
    BilinForm.toMatrix (Pi.basisFun R₂ n) = BilinForm.toMatrix' := by
  rw [BilinForm.toMatrix, BilinForm.toMatrix', LinearMap.toMatrix₂_basisFun]
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

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₂ M₂']
variable (c : Basis o R₂ M₂')
variable [DecidableEq o]

-- Cannot be a `simp` lemma because `b` must be inferred.
theorem BilinForm.toMatrix_comp (B : BilinForm R₂ M₂) (l r : M₂' →ₗ[R₂] M₂) :
    BilinForm.toMatrix c (B.comp l r) =
      (LinearMap.toMatrix c b l)ᵀ * BilinForm.toMatrix b B * LinearMap.toMatrix c b r :=
  LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _
#align bilin_form.to_matrix_comp BilinForm.toMatrix_comp

theorem BilinForm.toMatrix_compLeft (B : BilinForm R₂ M₂) (f : M₂ →ₗ[R₂] M₂) :
    BilinForm.toMatrix b (B.compLeft f) = (LinearMap.toMatrix b b f)ᵀ * BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂_comp _ _ _ B _
#align bilin_form.to_matrix_comp_left BilinForm.toMatrix_compLeft

theorem BilinForm.toMatrix_compRight (B : BilinForm R₂ M₂) (f : M₂ →ₗ[R₂] M₂) :
    BilinForm.toMatrix b (B.compRight f) = BilinForm.toMatrix b B * LinearMap.toMatrix b b f :=
  LinearMap.toMatrix₂_compl₂ _ _ _ B _
#align bilin_form.to_matrix_comp_right BilinForm.toMatrix_compRight

@[simp]
theorem BilinForm.toMatrix_mul_basis_toMatrix (c : Basis o R₂ M₂) (B : BilinForm R₂ M₂) :
    (b.toMatrix c)ᵀ * BilinForm.toMatrix b B * b.toMatrix c = BilinForm.toMatrix c B :=
  LinearMap.toMatrix₂_mul_basis_toMatrix _ _ _  _ B
#align bilin_form.to_matrix_mul_basis_to_matrix BilinForm.toMatrix_mul_basis_toMatrix

theorem BilinForm.mul_toMatrix_mul (B : BilinForm R₂ M₂) (M : Matrix o n R₂) (N : Matrix n o R₂) :
    M * BilinForm.toMatrix b B * N =
      BilinForm.toMatrix c (B.comp (Matrix.toLin c b Mᵀ) (Matrix.toLin c b N)) :=
  LinearMap.mul_toMatrix₂_mul _ _ _ _ B _ _
#align bilin_form.mul_to_matrix_mul BilinForm.mul_toMatrix_mul

theorem BilinForm.mul_toMatrix (B : BilinForm R₂ M₂) (M : Matrix n n R₂) :
    M * BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (Matrix.toLin b b Mᵀ)) :=
  LinearMap.mul_toMatrix₂ _ _ _ B _
#align bilin_form.mul_to_matrix BilinForm.mul_toMatrix

theorem BilinForm.toMatrix_mul (B : BilinForm R₂ M₂) (M : Matrix n n R₂) :
    BilinForm.toMatrix b B * M = BilinForm.toMatrix b (B.compRight (Matrix.toLin b b M)) :=
  LinearMap.toMatrix₂_mul _ _ _  B _
#align bilin_form.to_matrix_mul BilinForm.toMatrix_mul

theorem Matrix.toBilin_comp (M : Matrix n n R₂) (P Q : Matrix n o R₂) :
    (Matrix.toBilin b M).comp (toLin c b P) (toLin c b Q) = Matrix.toBilin c (Pᵀ * M * Q) := by
  ext x y
  rw [Matrix.toBilin, BilinForm.toMatrix, Matrix.toBilin, BilinForm.toMatrix, toMatrix₂_symm,
    toMatrix₂_symm, ← Matrix.toLinearMap₂_compl₁₂ b b c c]
  simp
#align matrix.to_bilin_comp Matrix.toBilin_comp

end ToMatrix

end Matrix

section MatrixAdjoints

open Matrix

variable {n : Type*} [Fintype n]
variable (b : Basis n R₃ M₃)
variable (J J₃ A A' : Matrix n n R₃)

@[simp]
theorem isAdjointPair_toBilin' [DecidableEq n] :
    BilinForm.IsAdjointPair (Matrix.toBilin' J) (Matrix.toBilin' J₃) (Matrix.toLin' A)
        (Matrix.toLin' A') ↔
      Matrix.IsAdjointPair J J₃ A A' :=
  isAdjointPair_toLinearMap₂' _ _ _ _
#align is_adjoint_pair_to_bilin' isAdjointPair_toBilin'

@[simp]
theorem isAdjointPair_toBilin [DecidableEq n] :
    BilinForm.IsAdjointPair (Matrix.toBilin b J) (Matrix.toBilin b J₃) (Matrix.toLin b b A)
        (Matrix.toLin b b A') ↔
      Matrix.IsAdjointPair J J₃ A A' :=
  isAdjointPair_toLinearMap₂ _ _ _ _ _ _
#align is_adjoint_pair_to_bilin isAdjointPair_toBilin

theorem Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₃) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A A' ↔
      J.IsAdjointPair J (P * A * P⁻¹) (P * A' * P⁻¹) :=
  Matrix.isAdjointPair_equiv _ _ _ _ h
#align matrix.is_adjoint_pair_equiv' Matrix.isAdjointPair_equiv'

variable [DecidableEq n]

/-- The submodule of pair-self-adjoint matrices with respect to bilinear forms corresponding to
given matrices `J`, `J₂`. -/
def pairSelfAdjointMatricesSubmodule' : Submodule R₃ (Matrix n n R₃) :=
  (BilinForm.isPairSelfAdjointSubmodule (Matrix.toBilin' J) (Matrix.toBilin' J₃)).map
    ((LinearMap.toMatrix' : ((n → R₃) →ₗ[R₃] n → R₃) ≃ₗ[R₃] Matrix n n R₃) :
      ((n → R₃) →ₗ[R₃] n → R₃) →ₗ[R₃] Matrix n n R₃)
#align pair_self_adjoint_matrices_submodule' pairSelfAdjointMatricesSubmodule'

theorem mem_pairSelfAdjointMatricesSubmodule' :
    A ∈ pairSelfAdjointMatricesSubmodule J J₃ ↔ Matrix.IsAdjointPair J J₃ A A := by
  simp only [mem_pairSelfAdjointMatricesSubmodule]
#align mem_pair_self_adjoint_matrices_submodule' mem_pairSelfAdjointMatricesSubmodule'

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def selfAdjointMatricesSubmodule' : Submodule R₃ (Matrix n n R₃) :=
  pairSelfAdjointMatricesSubmodule J J
#align self_adjoint_matrices_submodule' selfAdjointMatricesSubmodule'

theorem mem_selfAdjointMatricesSubmodule' :
    A ∈ selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A := by
  simp only [mem_selfAdjointMatricesSubmodule]
#align mem_self_adjoint_matrices_submodule' mem_selfAdjointMatricesSubmodule'

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skewAdjointMatricesSubmodule' : Submodule R₃ (Matrix n n R₃) :=
  pairSelfAdjointMatricesSubmodule (-J) J
#align skew_adjoint_matrices_submodule' skewAdjointMatricesSubmodule'

theorem mem_skewAdjointMatricesSubmodule' :
    A ∈ skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A := by
  simp only [mem_skewAdjointMatricesSubmodule]
#align mem_skew_adjoint_matrices_submodule' mem_skewAdjointMatricesSubmodule'

end MatrixAdjoints

namespace LinearMap

namespace BilinForm

section Det

open Matrix

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₃] (B₃ : BilinForm A M₃)
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem _root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin {M : Matrix ι ι R₂}
    (b : Basis ι R₂ M₂) : M.toBilin'.Nondegenerate ↔ (Matrix.toBilin b M).Nondegenerate :=
  (nondegenerate_congr_iff b.equivFun.symm).symm
#align matrix.nondegenerate_to_bilin'_iff_nondegenerate_to_bilin Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form
theorem _root_.Matrix.Nondegenerate.toBilin' {M : Matrix ι ι R₃} (h : M.Nondegenerate) :
    M.toBilin'.Nondegenerate := fun x hx =>
  h.eq_zero_of_ortho fun y => by simpa only [toBilin'_apply'] using hx y
#align matrix.nondegenerate.to_bilin' Matrix.Nondegenerate.toBilin'

@[simp]
theorem _root_.Matrix.nondegenerate_toBilin'_iff {M : Matrix ι ι R₃} :
    M.toBilin'.Nondegenerate ↔ M.Nondegenerate :=
  ⟨fun h v hv => h v fun w => (M.toBilin'_apply' _ _).trans <| hv w, Matrix.Nondegenerate.toBilin'⟩
#align matrix.nondegenerate_to_bilin'_iff Matrix.nondegenerate_toBilin'_iff

theorem _root_.Matrix.Nondegenerate.toBilin {M : Matrix ι ι R₃} (h : M.Nondegenerate)
    (b : Basis ι R₃ M₃) : (Matrix.toBilin b M).Nondegenerate :=
  (Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin b).mp h.toBilin'
#align matrix.nondegenerate.to_bilin Matrix.Nondegenerate.toBilin

@[simp]
theorem _root_.Matrix.nondegenerate_toBilin_iff {M : Matrix ι ι R₃} (b : Basis ι R₃ M₃) :
    (Matrix.toBilin b M).Nondegenerate ↔ M.Nondegenerate := by
  rw [← Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin, Matrix.nondegenerate_toBilin'_iff]
#align matrix.nondegenerate_to_bilin_iff Matrix.nondegenerate_toBilin_iff

/-! Lemmas transferring nondegeneracy between a bilinear form and its associated matrix -/

@[simp]
theorem nondegenerate_toMatrix'_iff {B : BilinForm R₃ (ι → R₃)} :
    B.toMatrix'.Nondegenerate (R := R₃) (m := ι) ↔ B.Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.symm.trans <| (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl
#align bilin_form.nondegenerate_to_matrix'_iff LinearMap.BilinForm.nondegenerate_toMatrix'_iff

theorem Nondegenerate.toMatrix' {B : BilinForm R₃ (ι → R₃)} (h : B.Nondegenerate) :
    B.toMatrix'.Nondegenerate :=
  nondegenerate_toMatrix'_iff.mpr h
#align bilin_form.nondegenerate.to_matrix' LinearMap.BilinForm.Nondegenerate.toMatrix'

@[simp]
theorem nondegenerate_toMatrix_iff {B : BilinForm R₃ M₃} (b : Basis ι R₃ M₃) :
    (BilinForm.toMatrix b B).Nondegenerate ↔ B.Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff b).symm.trans <| (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl
#align bilin_form.nondegenerate_to_matrix_iff LinearMap.BilinForm.nondegenerate_toMatrix_iff

theorem Nondegenerate.toMatrix {B : BilinForm R₃ M₃} (h : B.Nondegenerate) (b : Basis ι R₃ M₃) :
    (BilinForm.toMatrix b B).Nondegenerate :=
  (nondegenerate_toMatrix_iff b).mpr h
#align bilin_form.nondegenerate.to_matrix LinearMap.BilinForm.Nondegenerate.toMatrix

/-! Some shorthands for combining the above with `Matrix.nondegenerate_of_det_ne_zero` -/

theorem nondegenerate_toBilin'_iff_det_ne_zero {M : Matrix ι ι A} :
    M.toBilin'.Nondegenerate ↔ M.det ≠ 0 := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]
#align bilin_form.nondegenerate_to_bilin'_iff_det_ne_zero LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero

theorem nondegenerate_toBilin'_of_det_ne_zero' (M : Matrix ι ι A) (h : M.det ≠ 0) :
    M.toBilin'.Nondegenerate :=
  nondegenerate_toBilin'_iff_det_ne_zero.mpr h
#align bilin_form.nondegenerate_to_bilin'_of_det_ne_zero' LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'

theorem nondegenerate_iff_det_ne_zero {B : BilinForm A M₃} (b : Basis ι A M₃) :
    B.Nondegenerate ↔ (BilinForm.toMatrix b B).det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_toMatrix_iff]
#align bilin_form.nondegenerate_iff_det_ne_zero LinearMap.BilinForm.nondegenerate_iff_det_ne_zero

theorem nondegenerate_of_det_ne_zero (b : Basis ι A M₃) (h : (BilinForm.toMatrix b B₃).det ≠ 0) :
    B₃.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero b).mpr h
#align bilin_form.nondegenerate_of_det_ne_zero LinearMap.BilinForm.nondegenerate_of_det_ne_zero

end Det

end BilinForm

/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying
-/
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm

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
- `M₁` is a module over the commutative semiring `R₁`,
- `M₂` is a module over the commutative ring `R₂`.

## Tags

bilinear form, bilin form, BilinearForm, matrix, basis

-/

open LinearMap (BilinForm)
open Module

variable {R₁ : Type*} {M₁ : Type*} [CommSemiring R₁] [AddCommMonoid M₁] [Module R₁ M₁]
variable {R₂ : Type*} {M₂ : Type*} [CommRing R₂] [AddCommGroup M₂] [Module R₂ M₂]

section Matrix

variable {n o : Type*}

open Finset LinearMap Matrix

open Matrix

/-- The map from `Matrix n n R` to bilinear forms on `n → R`.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
def Matrix.toBilin'Aux [Fintype n] (M : Matrix n n R₁) : BilinForm R₁ (n → R₁) :=
  Matrix.toLinearMap₂'Aux _ _ M

theorem Matrix.toBilin'Aux_single [Fintype n] [DecidableEq n] (M : Matrix n n R₁) (i j : n) :
    M.toBilin'Aux (Pi.single i 1) (Pi.single j 1) = M i j :=
  Matrix.toLinearMap₂'Aux_single _ _ _ _ _

/-- The linear map from bilinear forms to `Matrix n n R` given an `n`-indexed basis.

This is an auxiliary definition for the equivalence `Matrix.toBilin'`. -/
def BilinForm.toMatrixAux (b : n → M₁) : BilinForm R₁ M₁ →ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂Aux R₁ b b

@[simp]
theorem LinearMap.BilinForm.toMatrixAux_apply (B : BilinForm R₁ M₁) (b : n → M₁) (i j : n) :
    BilinForm.toMatrixAux b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂Aux_apply R₁ B _ _ _ _

variable [Fintype n] [Fintype o]

theorem toBilin'Aux_toMatrixAux [DecidableEq n] (B₂ : BilinForm R₁ (n → R₁)) :
    Matrix.toBilin'Aux (BilinForm.toMatrixAux (fun j => Pi.single j 1) B₂) = B₂ := by
  rw [BilinForm.toMatrixAux, Matrix.toBilin'Aux, toLinearMap₂'Aux_toMatrix₂Aux]

section ToMatrix'

/-! ### `ToMatrix'` section

This section deals with the conversion between matrices and bilinear forms on `n → R₂`.
-/


variable [DecidableEq n] [DecidableEq o]

/-- The linear equivalence between bilinear forms on `n → R` and `n × n` matrices -/
def LinearMap.BilinForm.toMatrix' : BilinForm R₁ (n → R₁) ≃ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂' R₁

/-- The linear equivalence between `n × n` matrices and bilinear forms on `n → R` -/
def Matrix.toBilin' : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ (n → R₁) :=
  BilinForm.toMatrix'.symm

@[simp]
theorem Matrix.toBilin'Aux_eq (M : Matrix n n R₁) : Matrix.toBilin'Aux M = Matrix.toBilin' M :=
  rfl

theorem Matrix.toBilin'_apply (M : Matrix n n R₁) (x y : n → R₁) :
    Matrix.toBilin' M x y = ∑ i, ∑ j, x i * M i j * y j :=
  (Matrix.toLinearMap₂'_apply _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

theorem Matrix.toBilin'_apply' (M : Matrix n n R₁) (v w : n → R₁) :
    Matrix.toBilin' M v w = v ⬝ᵥ M *ᵥ w := Matrix.toLinearMap₂'_apply' _ _ _

@[simp]
theorem Matrix.toBilin'_single (M : Matrix n n R₁) (i j : n) :
    Matrix.toBilin' M (Pi.single i 1) (Pi.single j 1) = M i j := by
  simp [Matrix.toBilin'_apply, Pi.single_apply]

@[simp]
theorem LinearMap.BilinForm.toMatrix'_symm :
    (BilinForm.toMatrix'.symm : Matrix n n R₁ ≃ₗ[R₁] _) = Matrix.toBilin' :=
  rfl

@[simp]
theorem Matrix.toBilin'_symm :
    (Matrix.toBilin'.symm : _ ≃ₗ[R₁] Matrix n n R₁) = BilinForm.toMatrix' :=
  BilinForm.toMatrix'.symm_symm

@[simp]
theorem Matrix.toBilin'_toMatrix' (B : BilinForm R₁ (n → R₁)) :
    Matrix.toBilin' (BilinForm.toMatrix' B) = B :=
  Matrix.toBilin'.apply_symm_apply B

namespace LinearMap

@[simp]
theorem BilinForm.toMatrix'_toBilin' (M : Matrix n n R₁) :
    BilinForm.toMatrix' (Matrix.toBilin' M) = M :=
  (LinearMap.toMatrix₂' R₁).apply_symm_apply M

@[simp]
theorem BilinForm.toMatrix'_apply (B : BilinForm R₁ (n → R₁)) (i j : n) :
    BilinForm.toMatrix' B i j = B (Pi.single i 1) (Pi.single j 1) :=
  LinearMap.toMatrix₂'_apply _ _ _

@[simp]
theorem BilinForm.toMatrix'_comp (B : BilinForm R₁ (n → R₁)) (l r : (o → R₁) →ₗ[R₁] n → R₁) :
    (B.comp l r).toMatrix' = l.toMatrix'ᵀ * B.toMatrix' * r.toMatrix' :=
  B.toMatrix₂'_compl₁₂ _ _

theorem BilinForm.toMatrix'_compLeft (B : BilinForm R₁ (n → R₁)) (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (B.compLeft f).toMatrix' = f.toMatrix'ᵀ * B.toMatrix' :=
  B.toMatrix₂'_comp _

theorem BilinForm.toMatrix'_compRight (B : BilinForm R₁ (n → R₁)) (f : (n → R₁) →ₗ[R₁] n → R₁) :
    (B.compRight f).toMatrix' = B.toMatrix' * f.toMatrix' :=
  B.toMatrix₂'_compl₂ _

theorem BilinForm.mul_toMatrix'_mul (B : BilinForm R₁ (n → R₁)) (M : Matrix o n R₁)
    (N : Matrix n o R₁) : M * B.toMatrix' * N = (B.comp (Mᵀ).toLin' N.toLin').toMatrix' :=
  B.mul_toMatrix₂'_mul _ _

theorem BilinForm.mul_toMatrix' (B : BilinForm R₁ (n → R₁)) (M : Matrix n n R₁) :
    M * B.toMatrix' = (B.compLeft (Mᵀ).toLin').toMatrix' :=
  LinearMap.mul_toMatrix' B _

theorem BilinForm.toMatrix'_mul (B : BilinForm R₁ (n → R₁)) (M : Matrix n n R₁) :
    BilinForm.toMatrix' B * M = BilinForm.toMatrix' (B.compRight (Matrix.toLin' M)) :=
  B.toMatrix₂'_mul _

end LinearMap

theorem Matrix.toBilin'_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    M.toBilin'.comp P.toLin' Q.toLin' = (Pᵀ * M * Q).toBilin' :=
  BilinForm.toMatrix'.injective
    (by simp only [BilinForm.toMatrix'_comp, BilinForm.toMatrix'_toBilin', toMatrix'_toLin'])

end ToMatrix'

section ToMatrix

/-! ### `ToMatrix` section

This section deals with the conversion between matrices and bilinear forms on
a module with a fixed basis.
-/


variable [DecidableEq n] (b : Basis n R₁ M₁)

/-- `BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def BilinForm.toMatrix : BilinForm R₁ M₁ ≃ₗ[R₁] Matrix n n R₁ :=
  LinearMap.toMatrix₂ b b

/-- `BilinForm.toMatrix b` is the equivalence between `R`-bilinear forms on `M` and
`n`-by-`n` matrices with entries in `R`, if `b` is an `R`-basis for `M`. -/
noncomputable def Matrix.toBilin : Matrix n n R₁ ≃ₗ[R₁] BilinForm R₁ M₁ :=
  (BilinForm.toMatrix b).symm

@[simp]
theorem BilinForm.toMatrix_apply (B : BilinForm R₁ M₁) (i j : n) :
    BilinForm.toMatrix b B i j = B (b i) (b j) :=
  LinearMap.toMatrix₂_apply _ _ B _ _

theorem BilinForm.dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : n → R₁) :
    x ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ y = B (b.equivFun.symm x) (b.equivFun.symm y) := by
  simp only [dotProduct, mulVec_eq_sum, op_smul_eq_smul, Finset.sum_apply, Pi.smul_apply,
    transpose_apply, toMatrix_apply, smul_eq_mul, mul_sum, Basis.equivFun_symm_apply, map_sum,
    map_smul, coeFn_sum, LinearMap.smul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_)
  ring

lemma BilinForm.apply_eq_dotProduct_toMatrix_mulVec (B : BilinForm R₁ M₁) (x y : M₁) :
    B x y = (b.repr x) ⬝ᵥ (BilinForm.toMatrix b B) *ᵥ (b.repr y) := by
  nth_rw 1 [← b.sum_repr x, ← b.sum_repr y]
  suffices ∑ j, ∑ i, b.repr y j * b.repr x i * B (b i) (b j) =
           ∑ i, ∑ j, b.repr x i * b.repr y j * B (b i) (b j) by
    simpa [dotProduct, Matrix.mulVec_eq_sum, Finset.mul_sum, -Basis.sum_repr, ← mul_assoc]
  simp_rw [mul_comm (b.repr y _)]
  exact Finset.sum_comm

@[simp]
theorem Matrix.toBilin_apply (M : Matrix n n R₁) (x y : M₁) :
    Matrix.toBilin b M x y = ∑ i, ∑ j, b.repr x i * M i j * b.repr y j :=
  (Matrix.toLinearMap₂_apply _ _ _ _ _).trans
    (by simp only [smul_eq_mul, mul_comm, mul_left_comm])

-- Not a `simp` lemma since `BilinForm.toMatrix` needs an extra argument
theorem BilinearForm.toMatrixAux_eq (B : BilinForm R₁ M₁) :
    BilinForm.toMatrixAux (R₁ := R₁) b B = BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂Aux_eq _ _ B

@[simp]
theorem BilinForm.toMatrix_symm : (BilinForm.toMatrix b).symm = Matrix.toBilin b :=
  rfl

@[simp]
theorem Matrix.toBilin_symm : (Matrix.toBilin b).symm = BilinForm.toMatrix b :=
  (BilinForm.toMatrix b).symm_symm

theorem Matrix.toBilin_basisFun : Matrix.toBilin (Pi.basisFun R₁ n) = Matrix.toBilin' := by
  ext M
  simp only [coe_comp, coe_single, Function.comp_apply, toBilin_apply, Pi.basisFun_repr,
    toBilin'_apply]

theorem BilinForm.toMatrix_basisFun :
    BilinForm.toMatrix (Pi.basisFun R₁ n) = BilinForm.toMatrix' := by
  rw [BilinForm.toMatrix, BilinForm.toMatrix', LinearMap.toMatrix₂_basisFun]

@[simp]
theorem Matrix.toBilin_toMatrix (B : BilinForm R₁ M₁) :
    Matrix.toBilin b (BilinForm.toMatrix b B) = B :=
  (Matrix.toBilin b).apply_symm_apply B

@[simp]
theorem BilinForm.toMatrix_toBilin (M : Matrix n n R₁) :
    BilinForm.toMatrix b (Matrix.toBilin b M) = M :=
  (BilinForm.toMatrix b).apply_symm_apply M

variable {M₂' : Type*} [AddCommMonoid M₂'] [Module R₁ M₂']
variable (c : Basis o R₁ M₂')
variable [DecidableEq o]

-- Cannot be a `simp` lemma because `b` must be inferred.
theorem BilinForm.toMatrix_comp (B : BilinForm R₁ M₁) (l r : M₂' →ₗ[R₁] M₁) :
    BilinForm.toMatrix c (B.comp l r) =
      (LinearMap.toMatrix c b l)ᵀ * BilinForm.toMatrix b B * LinearMap.toMatrix c b r :=
  LinearMap.toMatrix₂_compl₁₂ _ _ _ _ B _ _

theorem BilinForm.toMatrix_compLeft (B : BilinForm R₁ M₁) (f : M₁ →ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compLeft f) = (LinearMap.toMatrix b b f)ᵀ * BilinForm.toMatrix b B :=
  LinearMap.toMatrix₂_comp _ _ _ B _

theorem BilinForm.toMatrix_compRight (B : BilinForm R₁ M₁) (f : M₁ →ₗ[R₁] M₁) :
    BilinForm.toMatrix b (B.compRight f) = BilinForm.toMatrix b B * LinearMap.toMatrix b b f :=
  LinearMap.toMatrix₂_compl₂ _ _ _ B _

@[simp]
theorem BilinForm.toMatrix_mul_basis_toMatrix (c : Basis o R₁ M₁) (B : BilinForm R₁ M₁) :
    (b.toMatrix c)ᵀ * BilinForm.toMatrix b B * b.toMatrix c = BilinForm.toMatrix c B :=
  LinearMap.toMatrix₂_mul_basis_toMatrix _ _ _  _ B

theorem BilinForm.mul_toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix o n R₁) (N : Matrix n o R₁) :
    M * BilinForm.toMatrix b B * N =
      BilinForm.toMatrix c (B.comp (Matrix.toLin c b Mᵀ) (Matrix.toLin c b N)) :=
  LinearMap.mul_toMatrix₂_mul _ _ _ _ B _ _

theorem BilinForm.mul_toMatrix (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    M * BilinForm.toMatrix b B = BilinForm.toMatrix b (B.compLeft (Matrix.toLin b b Mᵀ)) :=
  LinearMap.mul_toMatrix₂ _ _ _ B _

theorem BilinForm.toMatrix_mul (B : BilinForm R₁ M₁) (M : Matrix n n R₁) :
    BilinForm.toMatrix b B * M = BilinForm.toMatrix b (B.compRight (Matrix.toLin b b M)) :=
  LinearMap.toMatrix₂_mul _ _ _  B _

theorem Matrix.toBilin_comp (M : Matrix n n R₁) (P Q : Matrix n o R₁) :
    (Matrix.toBilin b M).comp (toLin c b P) (toLin c b Q) = Matrix.toBilin c (Pᵀ * M * Q) := by
  ext x y
  rw [Matrix.toBilin, BilinForm.toMatrix, Matrix.toBilin, BilinForm.toMatrix, toMatrix₂_symm,
    toMatrix₂_symm, ← Matrix.toLinearMap₂_compl₁₂ b b c c]
  simp

end ToMatrix

end Matrix

section MatrixAdjoints

open Matrix

variable {n : Type*} [Fintype n]
variable (b : Basis n R₂ M₂)
variable (J J₃ A A' : Matrix n n R₂)

theorem Matrix.isAdjointPair_equiv' [DecidableEq n] (P : Matrix n n R₂) (h : IsUnit P) :
    (Pᵀ * J * P).IsAdjointPair (Pᵀ * J * P) A A' ↔
      J.IsAdjointPair J (P * A * P⁻¹) (P * A' * P⁻¹) :=
  Matrix.isAdjointPair_equiv _ _ _ _ h

variable [DecidableEq n]

theorem mem_pairSelfAdjointMatricesSubmodule' :
    A ∈ pairSelfAdjointMatricesSubmodule J J₃ ↔ Matrix.IsAdjointPair J J₃ A A := by
  simp only [mem_pairSelfAdjointMatricesSubmodule]

/-- The submodule of self-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def selfAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂) :=
  pairSelfAdjointMatricesSubmodule J J

theorem mem_selfAdjointMatricesSubmodule' :
    A ∈ selfAdjointMatricesSubmodule J ↔ J.IsSelfAdjoint A := by
  simp only [mem_selfAdjointMatricesSubmodule]

/-- The submodule of skew-adjoint matrices with respect to the bilinear form corresponding to
the matrix `J`. -/
def skewAdjointMatricesSubmodule' : Submodule R₂ (Matrix n n R₂) :=
  pairSelfAdjointMatricesSubmodule (-J) J

theorem mem_skewAdjointMatricesSubmodule' :
    A ∈ skewAdjointMatricesSubmodule J ↔ J.IsSkewAdjoint A := by
  simp only [mem_skewAdjointMatricesSubmodule]

end MatrixAdjoints

namespace LinearMap

namespace BilinForm

section Det

open Matrix

variable {A : Type*} [CommRing A] [IsDomain A] [Module A M₂] (B₃ : BilinForm A M₂)
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

theorem _root_.Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin {M : Matrix ι ι R₁}
    (b : Basis ι R₁ M₁) : M.toBilin'.Nondegenerate ↔ (Matrix.toBilin b M).Nondegenerate :=
  (nondegenerate_congr_iff b.equivFun.symm).symm

-- Lemmas transferring nondegeneracy between a matrix and its associated bilinear form
theorem _root_.Matrix.Nondegenerate.toBilin' {M : Matrix ι ι R₂} (h : M.Nondegenerate) :
    M.toBilin'.Nondegenerate := fun x hx =>
  h.eq_zero_of_ortho fun y => by simpa only [toBilin'_apply'] using hx y

@[simp]
theorem _root_.Matrix.nondegenerate_toBilin'_iff {M : Matrix ι ι R₂} :
    M.toBilin'.Nondegenerate ↔ M.Nondegenerate := by
  refine ⟨fun h ↦ Matrix.nondegenerate_def.mpr ?_, Matrix.Nondegenerate.toBilin'⟩
  exact fun v hv => h v fun w => (M.toBilin'_apply' _ _).trans <| hv w

theorem _root_.Matrix.Nondegenerate.toBilin {M : Matrix ι ι R₂} (h : M.Nondegenerate)
    (b : Basis ι R₂ M₂) : (Matrix.toBilin b M).Nondegenerate :=
  (Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin b).mp h.toBilin'

@[simp]
theorem _root_.Matrix.nondegenerate_toBilin_iff {M : Matrix ι ι R₂} (b : Basis ι R₂ M₂) :
    (Matrix.toBilin b M).Nondegenerate ↔ M.Nondegenerate := by
  rw [← Matrix.nondegenerate_toBilin'_iff_nondegenerate_toBilin, Matrix.nondegenerate_toBilin'_iff]

/-! Lemmas transferring nondegeneracy between a bilinear form and its associated matrix -/

@[simp]
theorem nondegenerate_toMatrix'_iff {B : BilinForm R₂ (ι → R₂)} :
    B.toMatrix'.Nondegenerate (m := ι) ↔ B.Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.symm.trans <| (Matrix.toBilin'_toMatrix' B).symm ▸ Iff.rfl

theorem Nondegenerate.toMatrix' {B : BilinForm R₂ (ι → R₂)} (h : B.Nondegenerate) :
    B.toMatrix'.Nondegenerate :=
  nondegenerate_toMatrix'_iff.mpr h

@[simp]
theorem nondegenerate_toMatrix_iff {B : BilinForm R₂ M₂} (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).Nondegenerate ↔ B.Nondegenerate :=
  (Matrix.nondegenerate_toBilin_iff b).symm.trans <| (Matrix.toBilin_toMatrix b B).symm ▸ Iff.rfl

theorem Nondegenerate.toMatrix {B : BilinForm R₂ M₂} (h : B.Nondegenerate) (b : Basis ι R₂ M₂) :
    (BilinForm.toMatrix b B).Nondegenerate :=
  (nondegenerate_toMatrix_iff b).mpr h

/-! Some shorthands for combining the above with `Matrix.nondegenerate_of_det_ne_zero` -/

theorem nondegenerate_toBilin'_iff_det_ne_zero {M : Matrix ι ι A} :
    M.toBilin'.Nondegenerate ↔ M.det ≠ 0 := by
  rw [Matrix.nondegenerate_toBilin'_iff, Matrix.nondegenerate_iff_det_ne_zero]

theorem nondegenerate_toBilin'_of_det_ne_zero' (M : Matrix ι ι A) (h : M.det ≠ 0) :
    M.toBilin'.Nondegenerate :=
  nondegenerate_toBilin'_iff_det_ne_zero.mpr h

theorem nondegenerate_iff_det_ne_zero {B : BilinForm A M₂} (b : Basis ι A M₂) :
    B.Nondegenerate ↔ (BilinForm.toMatrix b B).det ≠ 0 := by
  rw [← Matrix.nondegenerate_iff_det_ne_zero, nondegenerate_toMatrix_iff]

theorem nondegenerate_of_det_ne_zero (b : Basis ι A M₂) (h : (BilinForm.toMatrix b B₃).det ≠ 0) :
    B₃.Nondegenerate :=
  (nondegenerate_iff_det_ne_zero b).mpr h

end Det

end BilinForm

end LinearMap

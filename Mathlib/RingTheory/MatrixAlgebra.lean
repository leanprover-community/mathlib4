/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.Data.Matrix.Kronecker
import Mathlib.RingTheory.TensorProduct.Basic


/-!
# Algebra isomorphisms between tensor products and matrices

We show `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/

suppress_compilation

open TensorProduct Algebra.TensorProduct Matrix

variable {R : Type*} [CommSemiring R]
variable {A B : Type*} [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable {m n : Type*}
variable (R A n)

namespace MatrixEquivTensor

/-- (Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-bilinear map.
-/
def toFunBilinear : A →ₗ[R] Matrix n n R →ₗ[R] Matrix n n A :=
  (Algebra.lsmul R R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix

@[simp]
theorem toFunBilinear_apply (a : A) (m : Matrix n n R) :
    toFunBilinear R A n a m = a • m.map (algebraMap R A) :=
  rfl

/-- (Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-linear map.
-/
def toFunLinear : A ⊗[R] Matrix n n R →ₗ[R] Matrix n n A :=
  TensorProduct.lift (toFunBilinear R A n)

variable [DecidableEq n] [Fintype n]

/-- The function `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`, as an algebra homomorphism.
-/
def toFunAlgHom : A ⊗[R] Matrix n n R →ₐ[R] Matrix n n A :=
  algHomOfLinearMapTensorProduct (toFunLinear R A n)
    (by
      intros
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply, Matrix.map_mul]
      ext
      dsimp
      simp_rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Finset.mul_sum,
        _root_.mul_assoc, Algebra.left_comm])
    (by
      simp_rw [toFunLinear, lift.tmul, toFunBilinear_apply,
        Matrix.map_one (algebraMap R A) (map_zero _) (map_one _), one_smul])

@[simp]
theorem toFunAlgHom_apply (a : A) (m : Matrix n n R) :
    toFunAlgHom R A n (a ⊗ₜ m) = a • m.map (algebraMap R A) := rfl

/-- (Implementation detail.)

The bare function `Matrix n n A → A ⊗[R] Matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (M : Matrix n n A) : A ⊗[R] Matrix n n R :=
  ∑ p : n × n, M p.1 p.2 ⊗ₜ stdBasisMatrix p.1 p.2 1

@[simp]
theorem invFun_zero : invFun R A n 0 = 0 := by simp [invFun]

@[simp]
theorem invFun_add (M N : Matrix n n A) :
    invFun R A n (M + N) = invFun R A n M + invFun R A n N := by
  simp [invFun, add_tmul, Finset.sum_add_distrib]

@[simp]
theorem invFun_smul (a : A) (M : Matrix n n A) :
    invFun R A n (a • M) = a ⊗ₜ 1 * invFun R A n M := by
  simp [invFun, Finset.mul_sum]

@[simp]
theorem invFun_algebraMap (M : Matrix n n R) : invFun R A n (M.map (algebraMap R A)) = 1 ⊗ₜ M := by
  dsimp [invFun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum, mul_boole]
  congr
  conv_rhs => rw [matrix_eq_sum_stdBasisMatrix M]
  convert Finset.sum_product (β := Matrix n n R) ..; simp

theorem right_inv (M : Matrix n n A) : (toFunAlgHom R A n) (invFun R A n M) = M := by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_stdBasisMatrix M]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Matrix.ext fun a b => ?_
  dsimp [stdBasisMatrix]
  split_ifs <;> aesop

theorem left_inv (M : A ⊗[R] Matrix n n R) : invFun R A n (toFunAlgHom R A n M) = M := by
  induction M with
  | zero => simp
  | tmul a m => simp
  | add x y hx hy =>
    rw [map_add]
    conv_rhs => rw [← hx, ← hy, ← invFun_add]

/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] Matrix n n R) ≃ Matrix n n A`.
-/
def equiv : A ⊗[R] Matrix n n R ≃ Matrix n n A where
  toFun := toFunAlgHom R A n
  invFun := invFun R A n
  left_inv := left_inv R A n
  right_inv := right_inv R A n

end MatrixEquivTensor

variable [Fintype n] [DecidableEq n]

/-- The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom R A n, MatrixEquivTensor.equiv R A n with }

open MatrixEquivTensor

@[simp]
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor R A n M = ∑ p : n × n, M p.1 p.2 ⊗ₜ stdBasisMatrix p.1 p.2 1 :=
  rfl

-- Porting note: short circuiting simplifier from simplifying left hand side
@[simp (high)]
theorem matrixEquivTensor_apply_stdBasisMatrix (i j : n) (x : A) :
    matrixEquivTensor R A n (stdBasisMatrix i j x) = x ⊗ₜ stdBasisMatrix i j 1 := by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, stdBasisMatrix]

@[deprecated (since := "2024-08-11")] alias matrixEquivTensor_apply_std_basis :=
  matrixEquivTensor_apply_stdBasisMatrix

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor R A n).symm (a ⊗ₜ M) = M.map fun x => a * algebraMap R A x :=
  rfl

variable (m) (B) [Fintype m] [DecidableEq m]

/-- A tensor product of matrices is equivalent as an algebra to a matrix of tensor products.

The forward map is the (tensor-ified) Kronecker product. -/
def matrixTensorAlgEquiv : Matrix m m A ⊗[R] Matrix n n B ≃ₐ[R] Matrix (m × n) (m × n) (A ⊗[R] B) :=
  Algebra.TensorProduct.congr (matrixEquivTensor R A m) (matrixEquivTensor R B n)
    |>.trans <| (Algebra.TensorProduct.tensorTensorTensorComm R A _ B _)
    |>.trans <|
      Algebra.TensorProduct.congr .refl (
        Algebra.TensorProduct.comm R _ _
          |>.trans <| (matrixEquivTensor R _ m).symm
          |>.trans <| Matrix.compAlgEquiv m n R R)
      |>.trans <| (matrixEquivTensor ..).symm

@[simp]
theorem matrixTensorAlgEquiv_symm_stdBasisMatrix_tmul
    (ia ja : m) (ib jb : n) (a : A) (b : B) :
    (matrixTensorAlgEquiv R A B m n).symm (stdBasisMatrix (ia, ib) (ja, jb) (a ⊗ₜ b)) =
      stdBasisMatrix ia ja a ⊗ₜ stdBasisMatrix ib jb b := by
  -- ext ⟨ia', ja'⟩ ⟨ib', jb'⟩
  dsimp [matrixTensorAlgEquiv, -matrixEquivTensor_apply]
  rw [matrixEquivTensor_apply_stdBasisMatrix]
  simp [-matrixEquivTensor_apply]
  congr <;> ext <;> simp [stdBasisMatrix]

theorem matrixTensorAlgEquiv_stdBasisMatrix_tmul_stdBasisMatrix
    (ia ja : m) (ib jb : n) (a : A) (b : B) :
    matrixTensorAlgEquiv R A B m n (stdBasisMatrix ia ja a ⊗ₜ stdBasisMatrix ib jb b) =
      stdBasisMatrix (ia, ib) (ja, jb) (a ⊗ₜ b) :=
  (matrixTensorAlgEquiv R A B m n).apply_eq_iff_eq_symm_apply.2 <|
    matrixTensorAlgEquiv_symm_stdBasisMatrix_tmul _ _ _ _ _ _ _ _ _ _ _ |>.symm

attribute [ext] ext_stdBasisMatrix
open scoped Kronecker
@[simp]
theorem matrixTensorAlgEquiv_tmul (a : Matrix m m A) (b : Matrix n n B) :
    matrixTensorAlgEquiv R A B m n (a ⊗ₜ b) = a ⊗ₖₜ b := by
  suffices
      (TensorProduct.mk R _ _).compr₂ (matrixTensorAlgEquiv R A B m n).toLinearMap =
        kroneckerTMulBilinear R from
    DFunLike.congr_fun (DFunLike.congr_fun this a) b
  ext ia ja a ib jb b : 4
  dsimp
  rw [matrixTensorAlgEquiv_stdBasisMatrix_tmul_stdBasisMatrix,
    kroneckerMap_stdBasisMatrix_stdBasisMatrix]
  all_goals simp

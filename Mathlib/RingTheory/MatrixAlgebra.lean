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

## Main definitions

* `matrixEquivTensor : Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
* `Matrix.kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[R] Matrix (m × n) (m × n) (A ⊗[R] B)`,
  where the forward map is the (tensor-ified) kronecker product.
-/

suppress_compilation

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R A B M N : Type*}
section Module

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Semiring A] [Semiring B]
variable [Module R M] [Module R N] [Algebra R A] [Algebra R B]
variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

open Kronecker

variable (l m n p R M N)

attribute [local ext] ext_linearMap

/-- `Matrix.kroneckerTMul` as a linear equivalence, when the two arguments are tensored. -/
def kroneckerTMulLinearEquiv :
    Matrix l m M ⊗[R] Matrix n p N ≃ₗ[R] Matrix (l × n) (m × p) (M ⊗[R] N) :=
  .ofLinear
    (TensorProduct.lift <| kroneckerTMulBilinear _)
    ((LinearMap.lsum R _ R fun ii => LinearMap.lsum R _ R fun jj => TensorProduct.map
      (stdBasisMatrixLinearMap R ii.1 jj.1) (stdBasisMatrixLinearMap R ii.2 jj.2))
      ∘ₗ (ofLinearEquiv R).symm.toLinearMap)
    (by
      ext : 4
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle,
        stdBasisMatrix_kroneckerTMul_stdBasisMatrix])
    (by
      ext : 5
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle,
        stdBasisMatrix_kroneckerTMul_stdBasisMatrix])

@[simp]
theorem kroneckerTMulLinearEquiv_tmul (a : Matrix l m M) (b : Matrix n p N) :
    kroneckerTMulLinearEquiv l m n p R M N (a ⊗ₜ b) = a ⊗ₖₜ b := rfl

@[simp]
theorem kroneckerTMulAlgEquiv_symm_stdBasisMatrix_tmul
    (ia : l) (ja : m) (ib : n) (jb : p) (a : M) (b : N) :
    (kroneckerTMulLinearEquiv l m n p R M N).symm (stdBasisMatrix (ia, ib) (ja, jb) (a ⊗ₜ b)) =
      stdBasisMatrix ia ja a ⊗ₜ stdBasisMatrix ib jb b := by
  rw [LinearEquiv.symm_apply_eq, kroneckerTMulLinearEquiv_tmul,
    stdBasisMatrix_kroneckerTMul_stdBasisMatrix]

@[simp]
theorem kroneckerTMulLinearEquiv_one :
    kroneckerTMulLinearEquiv m m n n R A B 1 = 1 := by simp [Algebra.TensorProduct.one_def]

/-- Note this can't be stated for rectangular matrices because there is no
`HMul (TensorProduct R _ _) (TensorProduct R _ _) (TensorProduct R _ _)` instance. -/
@[simp]
theorem kroneckerTMulLinearEquiv_mul :
    ∀ x y : Matrix m m A ⊗[R] Matrix n n B,
      kroneckerTMulLinearEquiv m m n n R A B (x * y) =
        kroneckerTMulLinearEquiv m m n n R A B x * kroneckerTMulLinearEquiv m m n n R A B y :=
  (kroneckerTMulLinearEquiv m m n n R A B).toLinearMap.map_mul_iff.2 <| by
    ext : 10
    simp [stdBasisMatrix_kroneckerTMul_stdBasisMatrix, mul_kroneckerTMul_mul]

end Module


variable [CommSemiring R]
variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable (n R A)

namespace MatrixEquivTensor

/-- (Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-bilinear map.
-/
def toFunBilinear : A →ₗ[R] Matrix n n R →ₗ[R] Matrix n n A :=
  (Algebra.lsmul R R (Matrix n n A)).toLinearMap.compl₂ (Algebra.linearMap R A).mapMatrix

@[simp]
theorem toFunBilinear_apply (a : A) (m : Matrix n n R) :
    toFunBilinear n R A a m = a • m.map (algebraMap R A) :=
  rfl

/-- (Implementation detail).
The function underlying `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`,
as an `R`-linear map.
-/
def toFunLinear : A ⊗[R] Matrix n n R →ₗ[R] Matrix n n A :=
  TensorProduct.lift (toFunBilinear n R A)

variable [DecidableEq n] [Fintype n]

/-- The function `(A ⊗[R] Matrix n n R) →ₐ[R] Matrix n n A`, as an algebra homomorphism.
-/
def toFunAlgHom : A ⊗[R] Matrix n n R →ₐ[R] Matrix n n A :=
  algHomOfLinearMapTensorProduct (toFunLinear n R A)
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
    toFunAlgHom n R A (a ⊗ₜ m) = a • m.map (algebraMap R A) := rfl

/-- (Implementation detail.)

The bare function `Matrix n n A → A ⊗[R] Matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (M : Matrix n n A) : A ⊗[R] Matrix n n R :=
  ∑ p : n × n, M p.1 p.2 ⊗ₜ stdBasisMatrix p.1 p.2 1

@[simp]
theorem invFun_zero : invFun n R A 0 = 0 := by simp [invFun]

@[simp]
theorem invFun_add (M N : Matrix n n A) :
    invFun n R A (M + N) = invFun n R A M + invFun n R A N := by
  simp [invFun, add_tmul, Finset.sum_add_distrib]

@[simp]
theorem invFun_smul (a : A) (M : Matrix n n A) :
    invFun n R A (a • M) = a ⊗ₜ 1 * invFun n R A M := by
  simp [invFun, Finset.mul_sum]

@[simp]
theorem invFun_algebraMap (M : Matrix n n R) : invFun n R A (M.map (algebraMap R A)) = 1 ⊗ₜ M := by
  dsimp [invFun]
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum, mul_boole]
  congr
  conv_rhs => rw [matrix_eq_sum_stdBasisMatrix M]
  convert Finset.sum_product (β := Matrix n n R) ..; simp

theorem right_inv (M : Matrix n n A) : (toFunAlgHom n R A) (invFun n R A M) = M := by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_stdBasisMatrix M]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Matrix.ext fun a b => ?_
  dsimp [stdBasisMatrix]
  split_ifs <;> aesop

theorem left_inv (M : A ⊗[R] Matrix n n R) : invFun n R A (toFunAlgHom n R A M) = M := by
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
  toFun := toFunAlgHom n R A
  invFun := invFun n R A
  left_inv := left_inv n R A
  right_inv := right_inv n R A

end MatrixEquivTensor

variable [Fintype n] [DecidableEq n]

/-- The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  AlgEquiv.symm { MatrixEquivTensor.toFunAlgHom n R A, MatrixEquivTensor.equiv n R A with }

open MatrixEquivTensor

@[simp]
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor n R A M = ∑ p : n × n, M p.1 p.2 ⊗ₜ stdBasisMatrix p.1 p.2 1 :=
  rfl

-- Porting note: short circuiting simplifier from simplifying left hand side
@[simp (high)]
theorem matrixEquivTensor_apply_stdBasisMatrix (i j : n) (x : A) :
    matrixEquivTensor n R A (stdBasisMatrix i j x) = x ⊗ₜ stdBasisMatrix i j 1 := by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, stdBasisMatrix]

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = a • M.map (algebraMap R A) :=
  rfl

namespace Matrix
open scoped Kronecker

variable (m) (B) [Fintype m] [DecidableEq m]

/-- `Matrix.kroneckerTMul` as an algebra equivalence, when the two arguments are tensored. -/
def kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[R] Matrix (m × n) (m × n) (A ⊗[R] B) :=
  .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R A B)
    (kroneckerTMulLinearEquiv_one _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _)

variable {m n A B}

@[simp]
theorem kroneckerTMulAlgEquiv_apply (x : Matrix m m A ⊗[R] Matrix n n B) :
    (kroneckerTMulAlgEquiv m n R A B) x = kroneckerTMulLinearEquiv m m n n R A B x :=
  rfl

@[simp]
theorem kroneckerTMulAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A ⊗[R] B)) :
    (kroneckerTMulAlgEquiv m n R A B).symm x = (kroneckerTMulLinearEquiv m m n n R A B).symm x :=
  rfl

end Matrix

/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.RingTheory.TensorProduct.Basic

/-!
We show `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/

suppress_compilation

universe u v w

open TensorProduct Algebra.TensorProduct Matrix

variable {n R A : Type*}

variable [CommSemiring R]
variable [Semiring A] [Algebra R A]
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

@[deprecated (since := "2024-08-11")] alias matrixEquivTensor_apply_std_basis :=
  matrixEquivTensor_apply_stdBasisMatrix

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = M.map fun x => a * algebraMap R A x :=
  rfl

/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison, Eric Wieser
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.TensorProduct.Basic


/-!
# Algebra isomorphisms between tensor products and matrices

## Main definitions

* `matrixEquivTensor : Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
* `Matrix.kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B)`,
  where the forward map is the (tensor-ified) Kronecker product.
-/

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R S A B M N : Type*}
section Module

variable [CommSemiring R] [Semiring S] [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Module R M] [Module S M] [Module R N]
variable [IsScalarTower R S M]
variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

open Kronecker

variable (l m n p R S A M N)

attribute [local ext] ext_linearMap

/-- `Matrix.kroneckerTMul` as a linear equivalence, when the two arguments are tensored. -/
def kroneckerTMulLinearEquiv :
    Matrix l m M ⊗[R] Matrix n p N ≃ₗ[S] Matrix (l × n) (m × p) (M ⊗[R] N) :=
  .ofLinear
    (AlgebraTensorModule.lift <| kroneckerTMulBilinear R S)
    (Matrix.liftLinear R fun ii jj =>
      AlgebraTensorModule.map (singleLinearMap S ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
    (by
      ext : 4
      simp [single_kroneckerTMul_single])
    (by
      ext : 5
      simp [single_kroneckerTMul_single])

@[simp]
theorem kroneckerTMulLinearEquiv_tmul (a : Matrix l m M) (b : Matrix n p N) :
    kroneckerTMulLinearEquiv l m n p R S M N (a ⊗ₜ b) = a ⊗ₖₜ b := rfl

@[simp]
theorem kroneckerTMulAlgEquiv_symm_single_tmul
    (ia : l) (ja : m) (ib : n) (jb : p) (a : M) (b : N) :
    (kroneckerTMulLinearEquiv l m n p R S M N).symm (single (ia, ib) (ja, jb) (a ⊗ₜ b)) =
      single ia ja a ⊗ₜ single ib jb b := by
  rw [LinearEquiv.symm_apply_eq, kroneckerTMulLinearEquiv_tmul,
    single_kroneckerTMul_single]

@[deprecated (since := "2025-05-05")]
alias kroneckerTMulAlgEquiv_symm_stdBasisMatrix_tmul := kroneckerTMulAlgEquiv_symm_single_tmul

@[simp]
theorem kroneckerTMulLinearEquiv_one [Module S A] [IsScalarTower R S A] :
    kroneckerTMulLinearEquiv m m n n R S A B 1 = 1 := by simp [Algebra.TensorProduct.one_def]

/-- Note this can't be stated for rectangular matrices because there is no
`HMul (TensorProduct R _ _) (TensorProduct R _ _) (TensorProduct R _ _)` instance. -/
@[simp]
theorem kroneckerTMulLinearEquiv_mul [Module S A] [IsScalarTower R S A] :
    ∀ x y : Matrix m m A ⊗[R] Matrix n n B,
      kroneckerTMulLinearEquiv m m n n R S A B (x * y) =
        kroneckerTMulLinearEquiv m m n n R S A B x * kroneckerTMulLinearEquiv m m n n R S A B y :=
  (kroneckerTMulLinearEquiv m m n n R S A B).toLinearMap.restrictScalars R |>.map_mul_iff.2 <| by
    ext : 10
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

/-- `Matrix.kronecker` as a linear equivalence, when the two arguments are tensored. -/
def kroneckerLinearEquiv :
    Matrix l m R ⊗[R] Matrix n p R ≃ₗ[R] Matrix (l × n) (m × p) R where
  toFun := (map · (Algebra.TensorProduct.lid R R).toRingHom) ∘
    (kroneckerTMulLinearEquiv l m n p R R R R)
  invFun := (kroneckerTMulLinearEquiv l m n p R R R R).symm ∘
    (map · (Algebra.TensorProduct.lid R R).symm)
  map_add' _ _ := by simp [Matrix.map_add]
  map_smul' _ _ := by simp [Matrix.map_smul]
  left_inv x := by simp [← AlgEquiv.coe_trans]
  right_inv x := by simp [← AlgEquiv.coe_trans]

variable {l m n p R}

@[simp] theorem kroneckerLinearEquiv_tmul (x : Matrix l m R) (y : Matrix n p R) :
    kroneckerLinearEquiv l m n p R (x ⊗ₜ y) = x ⊗ₖ y := rfl

@[simp] theorem kroneckerLinearEquiv_symm_kronecker (x : Matrix l m R) (y : Matrix n p R) :
    (kroneckerLinearEquiv l m n p R).symm (x ⊗ₖ y) = x ⊗ₜ y := by simp [LinearEquiv.symm_apply_eq]

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
  ∑ p : n × n, M p.1 p.2 ⊗ₜ single p.1 p.2 1

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
  simp only [Algebra.algebraMap_eq_smul_one, smul_tmul, ← tmul_sum]
  congr
  conv_rhs => rw [matrix_eq_sum_single M]
  convert Finset.sum_product (β := Matrix n n R) ..; simp

theorem right_inv (M : Matrix n n A) : (toFunAlgHom n R A) (invFun n R A M) = M := by
  simp only [invFun, map_sum, toFunAlgHom_apply]
  convert Finset.sum_product (β := Matrix n n A) ..
  conv_lhs => rw [matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Matrix.ext fun a b => ?_
  dsimp [single]
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
    matrixEquivTensor n R A M = ∑ p : n × n, M p.1 p.2 ⊗ₜ single p.1 p.2 1 :=
  rfl

-- High priority, to go before `matrixEquivTensor_apply`
@[simp high]
theorem matrixEquivTensor_apply_single (i j : n) (x : A) :
    matrixEquivTensor n R A (single i j x) = x ⊗ₜ single i j 1 := by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, single]

@[deprecated (since := "2025-05-05")]
alias matrixEquivTensor_apply_stdBasisMatrix := matrixEquivTensor_apply_single

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = a • M.map (algebraMap R A) :=
  rfl

namespace Matrix
open scoped Kronecker

variable (m) (S B)
variable [CommSemiring S] [Algebra R S] [Algebra S A] [IsScalarTower R S A]
variable [Fintype m] [DecidableEq m]

/-- `Matrix.kroneckerTMul` as an algebra equivalence, when the two arguments are tensored. -/
def kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B) :=
  .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R S A B)
    (kroneckerTMulLinearEquiv_one _ _ _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _ _ _)

variable {m n A B}

@[simp]
theorem kroneckerTMulAlgEquiv_apply (x : Matrix m m A ⊗[R] Matrix n n B) :
    (kroneckerTMulAlgEquiv m n R S A B) x = kroneckerTMulLinearEquiv m m n n R S A B x :=
  rfl

@[simp]
theorem kroneckerTMulAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) (A ⊗[R] B)) :
    (kroneckerTMulAlgEquiv m n R S A B).symm x =
      (kroneckerTMulLinearEquiv m m n n R S A B).symm x :=
  rfl

variable (m n) in
/-- `Matrix.kronecker` as an algebra equivalence, when the two arguments are tensored. -/
-- TODO: upgrade this to `≃⋆ₐ` for when `R` is a ⋆-ring (after #27290)
noncomputable def kroneckerAlgEquiv :
    (Matrix m m R ⊗[R] Matrix n n R) ≃ₐ[R] Matrix (m × n) (m × n) R :=
  .ofLinearEquiv (kroneckerLinearEquiv m m n n R)
    (by simp [Algebra.TensorProduct.one_def])
    fun x y ↦ by
      dsimp only [kroneckerLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
        AddHom.coe_mk, Function.comp_apply]
      rw [kroneckerTMulLinearEquiv_mul, Matrix.map_mul]

@[simp] theorem toLinearEquiv_kroneckerAlgEquiv :
    (kroneckerAlgEquiv m n R).toLinearEquiv = kroneckerLinearEquiv m m n n R := rfl

@[simp] theorem kroneckerAlgEquiv_apply (x : Matrix m m R ⊗ Matrix n n R) :
    kroneckerAlgEquiv m n R x = kroneckerLinearEquiv m m n n R x := rfl

@[simp] theorem kroneckerAlgEquiv_symm_apply (x : Matrix (m × n) (m × n) R) :
    (kroneckerAlgEquiv m n R).symm x = (kroneckerLinearEquiv m m n n R).symm x := rfl

end Matrix

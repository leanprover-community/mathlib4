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
* `tensorMatrixLinearEquiv : A ⊗[R] Matrix n n B ≃ₐ[S] Matrix n n (A ⊗[R] B)`
* `Matrix.kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B)`,
  where the forward map is the (tensor-ified) Kronecker product.
-/

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R S : Type*}
-- These are equipped with respectively `()`, `(1)`, `(*)`, with compatible module structures.
variable {M N M₁ N₁ A B : Type*}

section Module
variable [CommSemiring R] [Semiring S] [Algebra R S]

variable [AddCommMonoid M] [AddCommMonoid N]
variable [AddCommMonoidWithOne M₁] [AddCommMonoidWithOne N₁]
variable [NonUnitalSemiring A] [NonUnitalSemiring B]

variable [Module R M] [Module S M] [Module R N]
variable [Module R M₁] [Module S M₁] [Module R N₁]
variable [Module R A] [Module S A] [Module R B]
  [SMulCommClass R A A] [IsScalarTower R A A]
  [SMulCommClass R B B] [IsScalarTower R B B]

variable [IsScalarTower R S M] [IsScalarTower R S M₁] [IsScalarTower R S A]

section Kronecker
variable [Fintype l] [Fintype m] [Fintype n] [Fintype p]
variable [DecidableEq l] [DecidableEq m] [DecidableEq n] [DecidableEq p]

open Kronecker

variable (l m n p R S A B M N)

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
theorem kroneckerTMulLinearEquiv_one :
    kroneckerTMulLinearEquiv m m n n R S M₁ N₁ 1 = 1 := by simp [Algebra.TensorProduct.one_def]

/-- Note this can't be stated for rectangular matrices because there is no
`HMul (TensorProduct R _ _) (TensorProduct R _ _) (TensorProduct R _ _)` instance. -/
@[simp]
theorem kroneckerTMulLinearEquiv_mul :
    ∀ x y : Matrix m m A ⊗[R] Matrix n n B,
      kroneckerTMulLinearEquiv m m n n R S A B (x * y) =
        kroneckerTMulLinearEquiv m m n n R S A B x *
        kroneckerTMulLinearEquiv m m n n R S A B y :=
  (kroneckerTMulLinearEquiv m m n n R S A B).toLinearMap.restrictScalars R |>.map_mul_iff.2 <| by
    ext : 10
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

end Kronecker

theorem Matrix.map_single_tensorProductMk [DecidableEq m] [DecidableEq n]
    (i : m) (j : n) (a : M) (b : N) :
    (single i j b).map (a ⊗ₜ[R] ·) = single i j (a ⊗ₜ[R] b) :=
  map_single _ _ _ (TensorProduct.mk _ _ _ a)

variable (l m n p R S A B M N)

/-- Push a tensor product inside a matrix.

Note we have this in addition to `tensorMatrixLinearEquiv` as it works for infinite matrices. -/
def toTensorMatrixLin : M ⊗[R] Matrix m n N →ₗ[S] Matrix m n (M ⊗[R] N) :=
  AlgebraTensorModule.lift <| LinearMap.mapMatrixLinear _ ∘ₗ AlgebraTensorModule.mk _ _ _ _

@[simp low]
theorem toTensorMatrixLin_tmul (a : M) (b : Matrix m n N) :
    toTensorMatrixLin m n R S M N (a ⊗ₜ b) = b.map (fun x => a ⊗ₜ x) := rfl

@[simp high]
theorem toTensorMatrixLin_tmul_single [DecidableEq m] [DecidableEq n]
    (a : M) (i : m) (j : n) (b : N) :
    toTensorMatrixLin m n R S M N (a ⊗ₜ .single i j b) = .single i j (a ⊗ₜ b) := by
  simp_rw [toTensorMatrixLin_tmul, ← mk_apply, map_single]

variable (M₁ N₁) in
@[simp]
theorem toTensorMatrixLin_one [DecidableEq n] :
    toTensorMatrixLin n n R S M₁ N₁ 1 = 1 := by
  simp [Algebra.TensorProduct.one_def]

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

attribute [local ext] Matrix.ext_linearMap in
/-- The base change of matrices over modules. -/
def tensorMatrixLinearEquiv : M ⊗[R] Matrix m n N ≃ₗ[S] Matrix m n (M ⊗[R] N) :=
  .ofLinear
    (toTensorMatrixLin _ _ _ _ _ _)
    (Matrix.liftLinear ℕ fun i j =>
      AlgebraTensorModule.lift <|
        AlgebraTensorModule.mk R S M (Matrix m n N) |>.compl₂ (Matrix.singleLinearMap _ i j))
    (by ext; simp [-LinearMap.lsum_apply])
    (by ext; simp)

@[simp]
theorem tensorMatrixLinearEquiv_tmul_single (i : m) (j : n) (a : M) (b : N) :
    tensorMatrixLinearEquiv m n R S M N (a ⊗ₜ .single i j b) = Matrix.single i j (a ⊗ₜ[R] b) :=
  Matrix.map_single_tensorProductMk _ _ _ _

@[simp]
theorem tensorMatrixLinearEquiv_symm_single_tmul (i : m) (j : n) (a : M) (b : N) :
    (tensorMatrixLinearEquiv m n R S M N).symm (.single i j (a ⊗ₜ b)) = a ⊗ₜ .single i j b := by
  simp [tensorMatrixLinearEquiv]

attribute [local ext] Matrix.ext_linearMap in
@[simp]
theorem toTensorMatrixLin_mul (x y : A ⊗[R] Matrix n n B) :
    toTensorMatrixLin n n R S A B (x * y) =
      toTensorMatrixLin n n R S A B x * toTensorMatrixLin n n R S A B y := by
  classical
  revert x y
  erw [LinearMap.map_mul_iff _]
  ext xk xi xj xA yk yj yk yM : 8
  dsimp
  obtain rfl | hj := eq_or_ne xj yj
  · simp only [single_mul_single_same, ← mk_apply, map_single]
    simp
  · simp only [single_mul_single_of_ne _ _ _ _ hj, ← mk_apply, map_single]
    simp

end Module

section Algebra
variable [CommSemiring R] [CommSemiring S] [Algebra R S]
variable [Semiring A] [Semiring B]
variable [Algebra R A] [Algebra S A] [Algebra R B]
variable [IsScalarTower R S A]

variable (l m n p R S A B M N)

section tensorMatrixAlgEquiv
variable [Fintype n] [DecidableEq n]

/-- `toTensorMatrixLin` as an `AlgHom`. -/
@[simps!]
def toTensorMatrix : A ⊗[R] Matrix n n B →ₐ[S] Matrix n n (A ⊗[R] B) :=
  AlgHom.ofLinearMap
    (toTensorMatrixLin n n R S A B |>.restrictScalars S)
    (toTensorMatrixLin_one _ _ _ _ _)
    (toTensorMatrixLin_mul _ _ _ _ _)

/-- The base change of matrices over algebras.

This is the `AlgEquiv` version of `tensorMatrixLinearEquiv`. -/
def tensorMatrixAlgEquiv : A ⊗[R] Matrix n n B ≃ₐ[S] Matrix n n (A ⊗[R] B) where
  __ := toTensorMatrix n R S A B
  __ := tensorMatrixLinearEquiv n n R S A B

@[simp]
lemma tensorMatrixAlgEquiv_apply (M : A ⊗[R] Matrix n n B) :
    tensorMatrixAlgEquiv n R S A B M = toTensorMatrix n R S A B M := rfl

@[simp]
lemma tensorMatrixAlgEquiv_symm_apply (M : Matrix n n (A ⊗[R] B)) :
    (tensorMatrixAlgEquiv n R S A B).symm M = (tensorMatrixLinearEquiv n n R S A B).symm M := rfl

end tensorMatrixAlgEquiv

section matrixEquivTensor
variable [Fintype n] [DecidableEq n]

/-- The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`. -/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  Algebra.TensorProduct.rid _ _ _ |>.symm.mapMatrix |>.trans <|
    tensorMatrixAlgEquiv n R R A R |>.symm

@[simp]
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor n R A M = ∑ i : n, ∑ j : n, M i j ⊗ₜ single i j 1 := by
  simp [matrixEquivTensor, tensorMatrixLinearEquiv, liftLinear_apply]

-- Porting note: short circuiting simplifier from simplifying left hand side
@[simp (high)]
theorem matrixEquivTensor_apply_single (i j : n) (x : A) :
    matrixEquivTensor n R A (single i j x) = x ⊗ₜ single i j 1 := by
  simp [matrixEquivTensor]

@[deprecated (since := "2025-05-05")]
alias matrixEquivTensor_apply_stdBasisMatrix := matrixEquivTensor_apply_single

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = a • M.map (algebraMap R A) := by
  ext i j
  simp [matrixEquivTensor, Algebra.smul_def, Algebra.commutes (M i j) a]

end matrixEquivTensor

namespace Matrix
open scoped Kronecker

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

/-- `Matrix.kroneckerTMul` as an algebra equivalence, when the two arguments are tensored. -/
def kroneckerTMulAlgEquiv :
    Matrix m m A ⊗[R] Matrix n n B ≃ₐ[S] Matrix (m × n) (m × n) (A ⊗[R] B) :=
  .ofLinearEquiv (kroneckerTMulLinearEquiv m m n n R S A B)
    (kroneckerTMulLinearEquiv_one _ _ _ _)
    (kroneckerTMulLinearEquiv_mul _ _ _ _ _ _)

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

end Matrix

end Algebra

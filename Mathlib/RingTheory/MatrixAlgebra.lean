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

suppress_compilation

open TensorProduct Algebra.TensorProduct Matrix

variable {l m n p : Type*} {R S A B M N : Type*}
section Module

variable [CommSemiring R] [Semiring S] [Semiring A] [Semiring B] [AddCommMonoid M] [AddCommMonoid N]
variable [Algebra R S] [Algebra R A] [Algebra R B] [Module R M] [Module S M] [Module R N]
variable [IsScalarTower R S M]

section Kronecker
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

end Kronecker

variable (l m n p R S A M N)

/-- Push a tensor product inside a matrix. -/
def toTensorMatrixLin : A ⊗[R] Matrix m n M →ₗ[A] Matrix m n (A ⊗[R] M) :=
  AlgebraTensorModule.lift
    { toFun k := (TensorProduct.mk R _ _ k).mapMatrix
      map_add' k1 k2 := by ext : 2; simp [add_smul, single_add]
      map_smul' r k := by ext; dsimp; rw [← smul_eq_mul, smul_tmul'] }

@[simp low]
theorem toTensorMatrixLin_tmul (a : A) (b : Matrix m n M) :
    toTensorMatrixLin m n R A M (a ⊗ₜ b) = b.map (fun x => a ⊗ₜ x) := rfl

@[simp high]
theorem toTensorMatrixLin_tmul_single [DecidableEq m] [DecidableEq n]
    (a : A) (i : m) (j : n) (b : M) :
    toTensorMatrixLin m n R A M (a ⊗ₜ .single i j b) = .single i j (a ⊗ₜ b) := by
  simp_rw [toTensorMatrixLin_tmul, ← mk_apply, map_single]

variable [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

attribute [local ext] Matrix.ext_linearMap in
/-- The base change of matrices over modules. -/
def tensorMatrixLinearEquiv : A ⊗[R] Matrix m n M ≃ₗ[A] Matrix m n (A ⊗[R] M) :=
  .ofLinear
    (toTensorMatrixLin _ _ _ _ _)
    (Matrix.liftLinear ℕ fun i j =>
      AlgebraTensorModule.lift <|
        AlgebraTensorModule.mk R A A (Matrix m n M) |>.compl₂ (Matrix.singleLinearMap _ i j))
    (by
      ext : 4
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle])
    (by
      ext : 4
      dsimp [-LinearMap.lsum_apply]
      simp_rw [← mk_apply, map_single, mk_apply]
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle])

@[simp]
theorem tensorMatrixLinearEquiv_tmul_single (i : m) (j : n) (a : A) (b : M) :
    tensorMatrixLinearEquiv m n R A M (a ⊗ₜ .single i j b) = Matrix.single i j (a ⊗ₜ[R] b) := by
  simp [tensorMatrixLinearEquiv]

@[simp]
theorem tensorMatrixLinearEquiv_symm_single_tmul (i : m) (j : n) (a : A) (b : M) :
    (tensorMatrixLinearEquiv m n R A M).symm (.single i j (a ⊗ₜ b)) = a ⊗ₜ .single i j b := by
  simp [tensorMatrixLinearEquiv]

end Module

section Semiring
variable [CommSemiring R] [Semiring A] [Algebra R A]

variable (n R A M) in
@[simp]
theorem toTensorMatrixLin_one [DecidableEq n]
    [AddCommMonoidWithOne M] [Module R M] :
    toTensorMatrixLin n n R A M 1 = 1 := by
  simp [Algebra.TensorProduct.one_def]

attribute [local ext] Matrix.ext_linearMap in
@[simp]
theorem toTensorMatrixLin_mul [Fintype n] [NonUnitalSemiring B] [Module R B]
    [SMulCommClass R B B] [IsScalarTower R B B]
    (x y : A ⊗[R] Matrix n n B) :
    toTensorMatrixLin n n R A B (x * y) =
      toTensorMatrixLin n n R A B x * toTensorMatrixLin n n R A B y := by
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

end Semiring

section Algebra
variable (m n R S A B)

section tensorMatrixAlgEquiv

variable [Fintype n] [DecidableEq n]
variable [CommSemiring R] [CommSemiring S] [Semiring A]
variable [Algebra R A] [Algebra S A] [Semiring B] [Algebra R B] [SMulCommClass R S A]

/-- `toTensorMatrixLin` as an `AlgHom`. -/
@[simps!]
def toTensorMatrix : A ⊗[R] Matrix n n B →ₐ[S] Matrix n n (A ⊗[R] B) :=
  AlgHom.ofLinearMap
    (toTensorMatrixLin n n R A B |>.restrictScalars S)
    (toTensorMatrixLin_one _ _ _ _)
    toTensorMatrixLin_mul

/-- The base change of matrices over algebras.

This is the `AlgEquiv` version of `tensorMatrixLinearEquiv`. -/
def tensorMatrixAlgEquiv : A ⊗[R] Matrix n n B ≃ₐ[S] Matrix n n (A ⊗[R] B) where
  __ := toTensorMatrix n R S A B
  __ := tensorMatrixLinearEquiv n n R A B

@[simp]
lemma tensorMatrixAlgEquiv_apply (M : A ⊗[R] Matrix n n B) :
    tensorMatrixAlgEquiv n R S A B M = toTensorMatrix n R S A B M := rfl

@[simp]
lemma tensorMatrixAlgEquiv_symm_apply (M : Matrix n n (A ⊗[R] B)) :
    (tensorMatrixAlgEquiv n R S A B).symm M = (tensorMatrixLinearEquiv n n R A B).symm M := rfl

end tensorMatrixAlgEquiv

section matrixEquivTensor
variable [CommSemiring R] [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
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
  simp [matrixEquivTensor, toTensorMatrixLin_tmul_single]

@[deprecated (since := "2025-05-05")]
alias matrixEquivTensor_apply_stdBasisMatrix := matrixEquivTensor_apply_single

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = a • M.map (algebraMap R A) := by
  ext i j
  simp [matrixEquivTensor, TensorProduct.smul_tmul', Algebra.smul_def, Algebra.commutes (M i j) a]

end matrixEquivTensor

namespace Matrix
open scoped Kronecker

variable [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
variable [CommSemiring R] [CommSemiring S] [Semiring A] [Semiring B]
variable [Algebra R S] [Algebra R A] [Algebra S A] [Algebra R B] [IsScalarTower R S A]

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

end Matrix

end Algebra

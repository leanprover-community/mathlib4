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
* `matrixEquivTensorMatrix : K ⊗[F] Matrix n n A ≃ₐ[R] Matrix n n (K ⊗[F] A)`
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

end Module


variable [CommSemiring R]
variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable (n R A)

section

suppress_compilation

open scoped TensorProduct

variable (R K F A m n : Type*) [CommSemiring R] [Semiring K] [CommSemiring F] [Algebra R K]
    [Algebra F K] [Semiring A] [Algebra F A] [SMulCommClass F R K]

open Matrix

abbrev toTensorMatrixLin : K ⊗[F] Matrix m n A →ₗ[K] Matrix m n (K ⊗[F] A) :=
  AlgebraTensorModule.lift
    { toFun k := (TensorProduct.mk F _ _ k).mapMatrix
      map_add' k1 k2 := by ext; simp [add_smul]
      map_smul' r k := by ext; dsimp; rw [← smul_eq_mul, smul_tmul'] }

@[simp]
theorem toTensorMatrixLin_tmul (k : K) (M : Matrix m n A) :
    toTensorMatrixLin K F A m n (k ⊗ₜ M) = M.map (fun x => k ⊗ₜ x) := rfl

variable [DecidableEq m] [DecidableEq n]

@[simp high]
theorem toTensorMatrixLin_tmul_single (k : K) (i : m) (j : n) (a : A) :
    toTensorMatrixLin K F A m n (k ⊗ₜ .single i j a) = .single i j (k ⊗ₜ a) := by
  simp_rw [toTensorMatrixLin_tmul, ← mk_apply, map_single]

private abbrev invFun_toFun (i : m) (j : n) : K ⊗[F] A →ₗ[F] K ⊗[F] Matrix m n A :=
  AlgebraTensorModule.lift <|
    AlgebraTensorModule.mk F F K (Matrix m n A) |>.compl₂ (Matrix.singleLinearMap _ i j)

-- TODO: can we construct this by composition / lifting?
private abbrev invFun_Klinear (i : m) (j : n) : K ⊗[F] A →ₗ[K] K ⊗[F] Matrix m n A where
  __ := invFun_toFun K F A m n i j
  map_smul' k tensor := by
    induction tensor with
    | zero => simp
    | tmul k0 a => simp [smul_tmul', MulAction.mul_smul]
    | add _ _ h1 h2 => simp_all

variable [Fintype m] [Fintype n]

private def invFun_linearMap : Matrix m n (K ⊗[F] A) →ₗ[K] K ⊗[F] Matrix m n A :=
  Matrix.liftLinear ℕ (invFun_Klinear K F A m n)

@[simp]
theorem invFun_linearMap_single_tmul (i : m) (j : n) (k : K) (a : A) :
    invFun_linearMap K F A m n (.single i j (k ⊗ₜ a)) = k ⊗ₜ .single i j a := by
  simp [invFun_linearMap]

attribute [local ext] AlgebraTensorModule.ext Matrix.ext_linearMap in
def linearEquivTensor : K ⊗[F] Matrix m n A ≃ₗ[K] Matrix m n (K ⊗[F] A) :=
  .ofLinear
    (toTensorMatrixLin _ _ _ _ _)
    (invFun_linearMap _ _ _ _ _)
    (by
      ext : 4
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle])
    (by
      ext : 4
      dsimp [-LinearMap.lsum_apply]
      simp_rw [← mk_apply, map_single, mk_apply]
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle])

attribute [local ext] AlgebraTensorModule.ext Matrix.ext_linearMap in
theorem toTensorMatrixLin_mul (x y : K ⊗[F] Matrix n n A) :
    toTensorMatrixLin K F A n n (x * y) =
      toTensorMatrixLin K F A n n x * toTensorMatrixLin K F A n n y := by
  revert x y
  erw [LinearMap.map_mul_iff _]
  ext xk xi xj xA yk yj yk yM : 8
  dsimp
  obtain rfl | hj := eq_or_ne xj yj
  · simp only [single_mul_single_same, ← mk_apply, map_single]
    simp
  · simp only [single_mul_single_of_ne _ _ _ _ hj, ← mk_apply, map_single]
    simp

attribute [local ext] AlgebraTensorModule.ext
abbrev toTensorMatrix : K ⊗[F] Matrix n n A →ₐ[R] Matrix n n (K ⊗[F] A) :=
  AlgHom.ofLinearMap
    (toTensorMatrixLin K F A n n |>.restrictScalars R)
    (by simp [Algebra.TensorProduct.one_def])
    (toTensorMatrixLin_mul _ _ _ _)

/-- Base change of matrices. -/
def matrixEquivTensorMatrix : K ⊗[F] Matrix n n A ≃ₐ[R] Matrix n n (K ⊗[F] A) where
  __ := toTensorMatrix R K F A n
  __ := linearEquivTensor K F A n n

@[simp]
lemma matrixEquivTensorMatrix_apply (M : K ⊗[F] Matrix n n A) :
    matrixEquivTensorMatrix R K F A n M = toTensorMatrix R K F A n M := rfl

@[simp]
lemma matrixEquivTensorMatrix_symm_apply (M : Matrix n n (K ⊗[F] A)) :
    (matrixEquivTensorMatrix R K F A n).symm M = invFun_linearMap K F A n n M := rfl

end

variable [Fintype n] [DecidableEq n]

/-- The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  Algebra.TensorProduct.rid _ _ _|>.symm.mapMatrix|>.trans <|
    matrixEquivTensorMatrix R A R R n|>.symm

@[simp]
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor n R A M = ∑ i : n, ∑ j : n, M i j ⊗ₜ single i j 1 := by
  simp [matrixEquivTensor, invFun_linearMap, liftLinear_apply]

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

end Matrix

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
      (singleLinearMap R ii.1 jj.1) (singleLinearMap R ii.2 jj.2))
      ∘ₗ (ofLinearEquiv R).symm.toLinearMap)
    (by
      ext : 4
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle,
        single_kroneckerTMul_single])
    (by
      ext : 5
      simp [-LinearMap.lsum_apply, LinearMap.lsum_piSingle,
        single_kroneckerTMul_single])

@[simp]
theorem kroneckerTMulLinearEquiv_tmul (a : Matrix l m M) (b : Matrix n p N) :
    kroneckerTMulLinearEquiv l m n p R M N (a ⊗ₜ b) = a ⊗ₖₜ b := rfl

@[simp]
theorem kroneckerTMulAlgEquiv_symm_single_tmul
    (ia : l) (ja : m) (ib : n) (jb : p) (a : M) (b : N) :
    (kroneckerTMulLinearEquiv l m n p R M N).symm (single (ia, ib) (ja, jb) (a ⊗ₜ b)) =
      single ia ja a ⊗ₜ single ib jb b := by
  rw [LinearEquiv.symm_apply_eq, kroneckerTMulLinearEquiv_tmul,
    single_kroneckerTMul_single]

@[deprecated (since := "2025-05-05")]
alias kroneckerTMulAlgEquiv_symm_stdBasisMatrix_tmul := kroneckerTMulAlgEquiv_symm_single_tmul

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
    simp [single_kroneckerTMul_single, mul_kroneckerTMul_mul]

end Module


variable [CommSemiring R]
variable [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]
variable (n R A)

section

suppress_compilation

open scoped TensorProduct

variable (R K F A n: Type*) [CommSemiring R] [Semiring K] [CommSemiring F] [Algebra R K]
    [Algebra F K] [Semiring A] [Algebra F A] [DecidableEq n] [Fintype n] [SMulCommClass F R K]

open Matrix

/-- The `K`-bilinear map sending `(k, M)` to `k • (1 ⊗ M i j)ᵢⱼ` where
  `(1 ⊗ M i j)ᵢⱼ ∈ Mₙ(K ⊗ A)`. -/
private def toTensorMatrix_toFun_bilinear:
    K →ₗ[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) where
  toFun k := {
    toFun M := k • Algebra.TensorProduct.includeRight.mapMatrix M
    map_add' _ _ := by simp [← smul_add, map_add]
    map_smul' r M := by simpa using smul_comm _ _ _
  }
  map_add' k1 k2 := by ext; simp [add_smul]
  map_smul' r k := by ext; simp

@[simp]
lemma toTensorMatrix_toFun_bilinear_apply (k : K) (M : Matrix n n A) :
    toTensorMatrix_toFun_bilinear K F A n k M =
    k • Algebra.TensorProduct.includeRight.mapMatrix M := rfl

private abbrev toTensorMatrix_toFun_Flinear: K ⊗[F] Matrix n n A →ₗ[F] Matrix n n (K ⊗[F] A) :=
    TensorProduct.lift <| toTensorMatrix_toFun_bilinear K F A n

private abbrev toTensorMatrix_toFun_Kliniear: K ⊗[F] Matrix n n A →ₗ[K] Matrix n n (K ⊗[F] A) :=
  {__ := toTensorMatrix_toFun_Flinear K F A n,
   map_smul' k tensor := by
    induction tensor with
    | zero => simp
    | tmul k0 M => simp [TensorProduct.smul_tmul', MulAction.mul_smul]
    | add _ _ h1 h2 => simp_all}

private abbrev toTensorMatrix: K ⊗[F] Matrix n n A →ₐ[R] Matrix n n (K ⊗[F] A) :=
  AlgHom.ofLinearMap (toTensorMatrix_toFun_Kliniear K F A n)
  (by simp [Algebra.TensorProduct.one_def]) <| fun t1 t2 ↦ by
  induction t1 with
  | zero => simp
  | tmul x M =>
    induction t2 with
    | zero => simp
    | tmul x0 M' =>
        simp only [tmul_mul_tmul, LinearMap.coe_restrictScalars, LinearMap.coe_mk, lift.tmul',
          toTensorMatrix_toFun_bilinear_apply, AlgHom.mapMatrix_apply, smul_mul]
        rw [← AlgHom.coe_toRingHom, Matrix.map_mul, MulAction.mul_smul,
          ← smul_mul_assoc, ← smul_one_mul x0 (M'.map _), ← mul_assoc]
        congr 2
        rw [← map_one (f := Matrix.scalar n),
          show x0 • (scalar n) (1 : K ⊗[F] A) = scalar n (x0 • 1) from diagonal_smul _ _ |>.symm,
          ← Matrix.scalar_commute']
        · rw [← show x0 • (scalar n) (1 : K ⊗[F] A) = scalar n (x0 • 1) from
            diagonal_smul _ _ |>.symm, map_one, smul_one_mul]
        · intro i j
          simp [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', commute_iff_eq]
    | add _ _ h1 h2 => simp_all [mul_add]
  | add _ _ h1 h2 => simp_all [add_mul]

open TensorProduct

/-- The `K`-bilinear inverse sending `(k, a)` to `k ⊗ (a • E_ij)` for some `i j : n`. -/
private def invFun_toFun_bilinear (i j : n): K →ₗ[F] A →ₗ[F] K ⊗[F] Matrix n n A where
  toFun k := {
    toFun a := k ⊗ₜ single i j a
    map_add' _ _ := by simp [single_add, tmul_add]
    map_smul' _ _ := by simp [← smul_single, smul_tmul]
  }
  map_add' _ _ := by ext; simp [add_tmul]
  map_smul' _ _ := by ext; simp [smul_tmul']

omit [Fintype n] in
@[simp]
lemma invFun_toFun_bilinear_apply (i j : n) (k : K) (a : A) :
    invFun_toFun_bilinear K F A n i j k a = k ⊗ₜ single i j a := rfl

private abbrev invFun_toFun (i j : n) : K ⊗[F] A →ₗ[F] K ⊗[F] Matrix n n A :=
  TensorProduct.lift <| invFun_toFun_bilinear K F A n i j

private abbrev invFun_Klinear (i j : n): K ⊗[F] A →ₗ[K] K ⊗[F] Matrix n n A :=
  {__ := invFun_toFun K F A n i j,
   map_smul' k tensor := by
    induction tensor with
    | zero => simp
    | tmul k0 a => simp [smul_tmul', MulAction.mul_smul]
    | add _ _ h1 h2 => simp_all}

private abbrev invFun_linearMap: Matrix n n (K ⊗[F] A) →ₗ[K] K ⊗[F] Matrix n n A where
  toFun M := ∑ p : n × n, invFun_Klinear K F A n p.1 p.2 (M p.1 p.2)
  map_add' _ _ := by simp [Finset.sum_add_distrib]
  map_smul' _ _ := by simp [Finset.smul_sum]

lemma left_inv (M : K ⊗[F] Matrix n n A) :
    invFun_linearMap K F A n (toTensorMatrix R K F A n M) = M := by
  induction M with
  | zero => simp
  | tmul k M => simp [← tmul_sum, smul_tmul', Fintype.sum_prod_type, ← matrix_eq_sum_single]
  | add koxa1 koxa2 h1 h2 => rw [map_add, map_add, h1, h2]

lemma right_inv (M : Matrix n n (K ⊗[F] A)) :
    toTensorMatrix R K F A n (invFun_linearMap K F A n M) = M := by
  simp only [LinearMap.coe_mk, LinearMap.coe_toAddHom, AddHom.coe_mk, map_sum,
    AlgHom.ofLinearMap_apply, Fintype.sum_prod_type]
  conv_rhs => rw [matrix_eq_sum_single M]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  induction M p q with
  | zero => simp
  | tmul x y => simp [smul_tmul']
  | add _ _ h1 h2 => rw [map_add, map_add, h1, h2, single_add]

private def equivTensor' : K ⊗[F] Matrix n n A ≃ Matrix n n (K ⊗[F] A) where
  toFun := toTensorMatrix R K F A n
  invFun := invFun_linearMap K F A n
  left_inv := left_inv R K F A n
  right_inv := right_inv R K F A n

/-- The `R`-algebra isomorphism between `Mn(K ⊗[F] A)` and `K ⊗[F] Mₙ(A)`for `K` and `A` being
  `R`-algebras and `F`-algebras. -/
def matrixEquivTensorMatrix: K ⊗[F] Matrix n n A ≃ₐ[R] Matrix n n (K ⊗[F] A) :=
  {toTensorMatrix R K F A n, equivTensor' R K F A n with}

@[simp]
lemma matrixEquivTensorMatrix_apply (M : K ⊗[F] Matrix n n A) :
    matrixEquivTensorMatrix R K F A n M = toTensorMatrix R K F A n M := rfl

@[simp]
lemma matrixEquivTensorMatrix_symm_apply (M : Matrix n n (K ⊗[F] A)) :
    (matrixEquivTensorMatrix R K F A n).symm M = invFun_linearMap K F A n M := rfl

end

variable [Fintype n] [DecidableEq n]

/-- The `R`-algebra isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)`.
-/
def matrixEquivTensor : Matrix n n A ≃ₐ[R] A ⊗[R] Matrix n n R :=
  Algebra.TensorProduct.rid _ _ _|>.symm.mapMatrix|>.trans <|
    matrixEquivTensorMatrix R A R R n|>.symm

@[simp]
theorem matrixEquivTensor_apply (M : Matrix n n A) :
    matrixEquivTensor n R A M = ∑ p : n × n, M p.1 p.2 ⊗ₜ single p.1 p.2 1 :=
  rfl

-- Porting note: short circuiting simplifier from simplifying left hand side
@[simp (high)]
theorem matrixEquivTensor_apply_single (i j : n) (x : A) :
    matrixEquivTensor n R A (single i j x) = x ⊗ₜ single i j 1 := by
  have t : ∀ p : n × n, i = p.1 ∧ j = p.2 ↔ p = (i, j) := by aesop
  simp [ite_tmul, t, single]

@[deprecated (since := "2025-05-05")]
alias matrixEquivTensor_apply_stdBasisMatrix := matrixEquivTensor_apply_single

@[simp]
theorem matrixEquivTensor_apply_symm (a : A) (M : Matrix n n R) :
    (matrixEquivTensor n R A).symm (a ⊗ₜ M) = a • M.map (algebraMap R A) := by
  ext i j
  simp [matrixEquivTensor, TensorProduct.smul_tmul', Algebra.smul_def, Algebra.commutes (M i j) a]

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

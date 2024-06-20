/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix
import Mathlib.RingTheory.MatrixAlgebra

#align_import ring_theory.polynomial_algebra from "leanprover-community/mathlib"@"565eb991e264d0db702722b4bde52ee5173c9950"

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

Given `[CommRing R] [Ring A] [Algebra R A]`
we show `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
Combining this with the isomorphism `Matrix n n A ≃ₐ[R] (A ⊗[R] Matrix n n R)` proved earlier
in `RingTheory.MatrixAlgebra`, we obtain the algebra isomorphism
```
def matPolyEquiv :
    Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
```
which is characterized by
```
coeff (matPolyEquiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

universe u v w

open Polynomial TensorProduct

open Algebra.TensorProduct (algHomOfLinearMapTensorProduct includeLeft)

noncomputable section

variable (R A : Type*)
variable [CommSemiring R]
variable [Semiring A] [Algebra R A]

namespace PolyEquivTensor

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a bilinear function of two arguments.
-/
-- Porting note: was  `@[simps apply_apply]`
@[simps! apply_apply]
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap
#align poly_equiv_tensor.to_fun_bilinear PolyEquivTensor.toFunBilinear

theorem toFunBilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.sum fun n r => monomial n (a * algebraMap R A r) := by
  simp only [toFunBilinear_apply_apply, aeval_def, eval₂_eq_sum, Polynomial.sum, Finset.smul_sum]
  congr with i : 1
  rw [← Algebra.smul_def, ← C_mul', mul_smul_comm, C_mul_X_pow_eq_monomial, ← Algebra.commutes,
    ← Algebra.smul_def, smul_monomial]
#align poly_equiv_tensor.to_fun_bilinear_apply_eq_sum PolyEquivTensor.toFunBilinear_apply_eq_sum

/-- (Implementation detail).
The function underlying `A ⊗[R] R[X] →ₐ[R] A[X]`,
as a linear map.
-/
def toFunLinear : A ⊗[R] R[X] →ₗ[R] A[X] :=
  TensorProduct.lift (toFunBilinear R A)
#align poly_equiv_tensor.to_fun_linear PolyEquivTensor.toFunLinear

@[simp]
theorem toFunLinear_tmul_apply (a : A) (p : R[X]) :
    toFunLinear R A (a ⊗ₜ[R] p) = toFunBilinear R A a p :=
  rfl
#align poly_equiv_tensor.to_fun_linear_tmul_apply PolyEquivTensor.toFunLinear_tmul_apply

-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
theorem toFunLinear_mul_tmul_mul_aux_1 (p : R[X]) (k : ℕ) (h : Decidable ¬p.coeff k = 0) (a : A) :
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 =
    a * (algebraMap R A) (coeff p k) := by classical split_ifs <;> simp [*]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_1 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1

theorem toFunLinear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.antidiagonal k).sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) := by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  congr
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, RingHom.map_mul]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2

theorem toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) ⊗ₜ[R] (p₁ * p₂)) =
      (toFunLinear R A) (a₁ ⊗ₜ[R] p₁) * (toFunLinear R A) (a₂ ⊗ₜ[R] p₂) := by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne]
    conv_rhs => rw [coeff_mul]
    simp_rw [finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne, mul_ite,
      mul_zero, ite_mul, zero_mul]
    simp_rw [← ite_zero_mul (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
    simp_rw [← mul_ite_zero (¬coeff p₂ _ = 0) _ (_ * _)]
    simp_rw [toFunLinear_mul_tmul_mul_aux_1, toFunLinear_mul_tmul_mul_aux_2]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul PolyEquivTensor.toFunLinear_mul_tmul_mul

theorem toFunLinear_one_tmul_one :
    toFunLinear R A (1 ⊗ₜ[R] 1) = 1 := by
  rw [toFunLinear_tmul_apply, toFunBilinear_apply_apply, Polynomial.aeval_one, one_smul]
#align poly_equiv_tensor.to_fun_linear_algebra_map_tmul_one PolyEquivTensor.toFunLinear_one_tmul_oneₓ

/-- (Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] A[X]`.
-/
def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_one_tmul_one R A)
#align poly_equiv_tensor.to_fun_alg_hom PolyEquivTensor.toFunAlgHom

@[simp]
theorem toFunAlgHom_apply_tmul (a : A) (p : R[X]) :
    toFunAlgHom R A (a ⊗ₜ[R] p) = p.sum fun n r => monomial n (a * (algebraMap R A) r) :=
  toFunBilinear_apply_eq_sum R A _ _
#align poly_equiv_tensor.to_fun_alg_hom_apply_tmul PolyEquivTensor.toFunAlgHom_apply_tmul

/-- (Implementation detail.)

The bare function `A[X] → A ⊗[R] R[X]`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def invFun (p : A[X]) : A ⊗[R] R[X] :=
  p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X]))
#align poly_equiv_tensor.inv_fun PolyEquivTensor.invFun

@[simp]
theorem invFun_add {p q} : invFun R A (p + q) = invFun R A p + invFun R A q := by
  simp only [invFun, eval₂_add]
#align poly_equiv_tensor.inv_fun_add PolyEquivTensor.invFun_add

theorem invFun_monomial (n : ℕ) (a : A) :
    invFun R A (monomial n a) = (a ⊗ₜ[R] 1) * 1 ⊗ₜ[R] X ^ n :=
  eval₂_monomial _ _
#align poly_equiv_tensor.inv_fun_monomial PolyEquivTensor.invFun_monomial

theorem left_inv (x : A ⊗ R[X]) : invFun R A ((toFunAlgHom R A) x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
  · intro a p
    dsimp only [invFun]
    rw [toFunAlgHom_apply_tmul, eval₂_sum]
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, ← Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_pow_eq p]
    simp only [Algebra.smul_def]
    rfl
  · intro p q hp hq
    simp only [AlgHom.map_add, invFun_add, hp, hq]
#align poly_equiv_tensor.left_inv PolyEquivTensor.left_inv

theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x := by
  refine Polynomial.induction_on' x ?_ ?_
  · intro p q hp hq
    simp only [invFun_add, AlgHom.map_add, hp, hq]
  · intro n a
    rw [invFun_monomial, Algebra.TensorProduct.tmul_pow,
        one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, toFunAlgHom_apply_tmul,
        X_pow_eq_monomial, sum_monomial_index] <;>
      simp
#align poly_equiv_tensor.right_inv PolyEquivTensor.right_inv

/-- (Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] R[X]) ≃ A[X]`.
-/
def equiv : A ⊗[R] R[X] ≃ A[X] where
  toFun := toFunAlgHom R A
  invFun := invFun R A
  left_inv := left_inv R A
  right_inv := right_inv R A
#align poly_equiv_tensor.equiv PolyEquivTensor.equiv

end PolyEquivTensor

open PolyEquivTensor

/-- The `R`-algebra isomorphism `A[X] ≃ₐ[R] (A ⊗[R] R[X])`.
-/
def polyEquivTensor : A[X] ≃ₐ[R] A ⊗[R] R[X] :=
  AlgEquiv.symm { PolyEquivTensor.toFunAlgHom R A, PolyEquivTensor.equiv R A with }
#align poly_equiv_tensor polyEquivTensor

@[simp]
theorem polyEquivTensor_apply (p : A[X]) :
    polyEquivTensor R A p =
      p.eval₂ (includeLeft : A →ₐ[R] A ⊗[R] R[X]) ((1 : A) ⊗ₜ[R] (X : R[X])) :=
  rfl
#align poly_equiv_tensor_apply polyEquivTensor_apply

@[simp]
theorem polyEquivTensor_symm_apply_tmul (a : A) (p : R[X]) :
    (polyEquivTensor R A).symm (a ⊗ₜ p) = p.sum fun n r => monomial n (a * algebraMap R A r) :=
  toFunAlgHom_apply_tmul _ _ _ _
#align poly_equiv_tensor_symm_apply_tmul polyEquivTensor_symm_apply_tmul

open DMatrix Matrix

variable {R}
variable {n : Type w} [DecidableEq n] [Fintype n]

/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`matPolyEquiv_coeff_apply` below.)
-/
noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor R R[X] n).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm
#align mat_poly_equiv matPolyEquiv

@[simp] theorem matPolyEquiv_symm_C (M : Matrix n n R) : matPolyEquiv.symm (C M) = M.map C := by
  simp [matPolyEquiv, ← C_eq_algebraMap]

@[simp] theorem matPolyEquiv_map_C (M : Matrix n n R) : matPolyEquiv (M.map C) = C M := by
  rw [← matPolyEquiv_symm_C, AlgEquiv.apply_symm_apply]

@[simp] theorem matPolyEquiv_symm_X :
    matPolyEquiv.symm X = diagonal fun _ : n => (X : R[X]) := by
  suffices (Matrix.map 1 fun x ↦ X * algebraMap R R[X] x) = diagonal fun _ : n => (X : R[X]) by
    simpa [matPolyEquiv]
  rw [← Matrix.diagonal_one]
  simp [-Matrix.diagonal_one]

@[simp] theorem matPolyEquiv_diagonal_X :
    matPolyEquiv (diagonal fun _ : n => (X : R[X])) = X := by
  rw [← matPolyEquiv_symm_X, AlgEquiv.apply_symm_apply]

open Finset

theorem matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
    matPolyEquiv (stdBasisMatrix i j <| monomial k x) = monomial k (stdBasisMatrix i j x) := by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_std_basis]
  apply (polyEquivTensor R (Matrix n n R)).injective
  simp only [AlgEquiv.apply_symm_apply,Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, Matrix.mul_one,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.includeLeft_apply]
  rw [← smul_X_eq_monomial, ← TensorProduct.smul_tmul]
  congr with i' <;> simp [stdBasisMatrix]
#align mat_poly_equiv_coeff_apply_aux_1 matPolyEquiv_coeff_apply_aux_1

theorem matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : ℕ) :
    coeff (matPolyEquiv (stdBasisMatrix i j p)) k = stdBasisMatrix i j (coeff p k) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, DMatrix.add_apply, stdBasisMatrix_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp
#align mat_poly_equiv_coeff_apply_aux_2 matPolyEquiv_coeff_apply_aux_2

@[simp]
theorem matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : ℕ) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k := by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    erw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [stdBasisMatrix]
    split_ifs <;> rename_i h
    · rcases h with ⟨rfl, rfl⟩
      simp [stdBasisMatrix]
    · simp [stdBasisMatrix, h]
#align mat_poly_equiv_coeff_apply matPolyEquiv_coeff_apply

@[simp]
theorem matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : ℕ) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j := by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]
#align mat_poly_equiv_symm_apply_coeff matPolyEquiv_symm_apply_coeff

theorem matPolyEquiv_smul_one (p : R[X]) :
    matPolyEquiv (p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R)) := by
  ext m i j
  simp only [matPolyEquiv_coeff_apply, smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, coeff_map, algebraMap_matrix_apply, Algebra.id.map_eq_id, RingHom.id_apply]
  split_ifs <;> simp
#align mat_poly_equiv_smul_one matPolyEquiv_smul_one

@[simp]
lemma matPolyEquiv_map_smul (p : R[X]) (M : Matrix n n R[X]) :
    matPolyEquiv (p • M) = p.map (algebraMap _ _) * matPolyEquiv M := by
  rw [← one_mul M, ← smul_mul_assoc, _root_.map_mul, matPolyEquiv_smul_one, one_mul]

theorem support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) ⊆ support (matPolyEquiv m) := by
  intro k
  contrapose
  simp only [not_mem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply, hk]
  rfl
#align support_subset_support_mat_poly_equiv support_subset_support_matPolyEquiv

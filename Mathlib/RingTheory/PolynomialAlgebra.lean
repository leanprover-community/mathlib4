/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.Data.Polynomial.AlgebraMap
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.DMatrix

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
-- porting note: was  `@[simps apply_apply]`
@[simps! apply_apply]
def toFunBilinear : A →ₗ[A] R[X] →ₗ[R] A[X] :=
  LinearMap.toSpanSingleton A _ (aeval (Polynomial.X : A[X])).toLinearMap
#align poly_equiv_tensor.to_fun_bilinear PolyEquivTensor.toFunBilinear

theorem toFunBilinear_apply_eq_sum (a : A) (p : R[X]) :
    toFunBilinear R A a p = p.sum fun n r => monomial n (a * algebraMap R A r) := by
  simp only [toFunBilinear_apply_apply, aeval_def, eval₂_eq_sum, Polynomial.sum, Finset.smul_sum]
  -- ⊢ (Finset.sum (support p) fun x => a • (↑(algebraMap R A[X]) (coeff p x) * X ^ …
  congr with i : 1
  -- ⊢ a • (↑(algebraMap R A[X]) (coeff p i) * X ^ i) = ↑(monomial i) (a * ↑(algebr …
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
    ite (¬coeff p k = 0) (a * (algebraMap R A) (coeff p k)) 0 = a * (algebraMap R A) (coeff p k) :=
  by classical split_ifs <;> simp [*]
     -- 🎉 no goals
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_1 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_1

theorem toFunLinear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    a₁ * a₂ * (algebraMap R A) ((p₁ * p₂).coeff k) =
      (Finset.Nat.antidiagonal k).sum fun x =>
        a₁ * (algebraMap R A) (coeff p₁ x.1) * (a₂ * (algebraMap R A) (coeff p₂ x.2)) := by
  simp_rw [mul_assoc, Algebra.commutes, ← Finset.mul_sum, mul_assoc, ← Finset.mul_sum]
  -- ⊢ a₁ * (a₂ * ↑(algebraMap R A) (coeff (p₁ * p₂) k)) = a₁ * (a₂ * Finset.sum (F …
  congr
  -- ⊢ ↑(algebraMap R A) (coeff (p₁ * p₂) k) = Finset.sum (Finset.Nat.antidiagonal  …
  simp_rw [Algebra.commutes (coeff p₂ _), coeff_mul, map_sum, RingHom.map_mul]
  -- 🎉 no goals
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul_aux_2 PolyEquivTensor.toFunLinear_mul_tmul_mul_aux_2

theorem toFunLinear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : R[X]) :
    (toFunLinear R A) ((a₁ * a₂) ⊗ₜ[R] (p₁ * p₂)) =
      (toFunLinear R A) (a₁ ⊗ₜ[R] p₁) * (toFunLinear R A) (a₂ ⊗ₜ[R] p₂) := by
  classical
    simp only [toFunLinear_tmul_apply, toFunBilinear_apply_eq_sum]
    ext k
    simp_rw [coeff_sum, coeff_monomial, sum_def, Finset.sum_ite_eq', mem_support_iff, Ne.def]
    conv_rhs => rw [coeff_mul]
    simp_rw [finset_sum_coeff, coeff_monomial, Finset.sum_ite_eq', mem_support_iff, Ne.def, mul_ite,
      mul_zero, ite_mul, zero_mul]
    simp_rw [ite_mul_zero_left (¬coeff p₁ _ = 0) (a₁ * (algebraMap R A) (coeff p₁ _))]
    simp_rw [ite_mul_zero_right (¬coeff p₂ _ = 0) _ (_ * _)]
    simp_rw [toFunLinear_mul_tmul_mul_aux_1, toFunLinear_mul_tmul_mul_aux_2]
#align poly_equiv_tensor.to_fun_linear_mul_tmul_mul PolyEquivTensor.toFunLinear_mul_tmul_mul

theorem toFunLinear_algebraMap_tmul_one (r : R) :
    (toFunLinear R A) ((algebraMap R A) r ⊗ₜ[R] 1) = (algebraMap R A[X]) r := by
  rw [toFunLinear_tmul_apply, toFunBilinear_apply_apply, Polynomial.aeval_one, algebraMap_smul,
    Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one] -- porting note: had to
  -- add extra `Algebra.algebraMap_eq_smul_one`
#align poly_equiv_tensor.to_fun_linear_algebra_map_tmul_one PolyEquivTensor.toFunLinear_algebraMap_tmul_one

/-- (Implementation detail).
The algebra homomorphism `A ⊗[R] R[X] →ₐ[R] A[X]`.
-/
def toFunAlgHom : A ⊗[R] R[X] →ₐ[R] A[X] :=
  algHomOfLinearMapTensorProduct (toFunLinear R A) (toFunLinear_mul_tmul_mul R A)
    (toFunLinear_algebraMap_tmul_one R A)
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
  -- 🎉 no goals
#align poly_equiv_tensor.inv_fun_add PolyEquivTensor.invFun_add

theorem invFun_monomial (n : ℕ) (a : A) :
    invFun R A (monomial n a) = (a ⊗ₜ[R] 1) * 1 ⊗ₜ[R] X ^ n :=
  eval₂_monomial _ _
#align poly_equiv_tensor.inv_fun_monomial PolyEquivTensor.invFun_monomial

theorem left_inv (x : A ⊗ R[X]) : invFun R A ((toFunAlgHom R A) x) = x := by
  refine TensorProduct.induction_on x ?_ ?_ ?_
  · simp [invFun]
    -- 🎉 no goals
  · intro a p
    -- ⊢ invFun R A (↑(toFunAlgHom R A) (a ⊗ₜ[R] p)) = a ⊗ₜ[R] p
    dsimp only [invFun]
    -- ⊢ eval₂ (↑includeLeft) (1 ⊗ₜ[R] X) (↑(toFunAlgHom R A) (a ⊗ₜ[R] p)) = a ⊗ₜ[R] p
    rw [toFunAlgHom_apply_tmul, eval₂_sum]
    -- ⊢ (sum p fun n a_1 => eval₂ (↑includeLeft) (1 ⊗ₜ[R] X) (↑(monomial n) (a * ↑(a …
    simp_rw [eval₂_monomial, AlgHom.coe_toRingHom, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
      one_mul, ← Algebra.commutes, ← Algebra.smul_def, smul_tmul, sum_def, ← tmul_sum]
    conv_rhs => rw [← sum_C_mul_X_pow_eq p]
    -- ⊢ (a ⊗ₜ[R] Finset.sum (support p) fun a => coeff p a • X ^ a) = a ⊗ₜ[R] sum p  …
    simp only [Algebra.smul_def]
    -- ⊢ (a ⊗ₜ[R] Finset.sum (support p) fun x => ↑(algebraMap R R[X]) (coeff p x) *  …
    rfl
    -- 🎉 no goals
  · intro p q hp hq
    -- ⊢ invFun R A (↑(toFunAlgHom R A) (p + q)) = p + q
    simp only [AlgHom.map_add, invFun_add, hp, hq]
    -- 🎉 no goals
#align poly_equiv_tensor.left_inv PolyEquivTensor.left_inv

theorem right_inv (x : A[X]) : (toFunAlgHom R A) (invFun R A x) = x := by
  refine Polynomial.induction_on' x ?_ ?_
  -- ⊢ ∀ (p q : A[X]), ↑(toFunAlgHom R A) (invFun R A p) = p → ↑(toFunAlgHom R A) ( …
  · intro p q hp hq
    -- ⊢ ↑(toFunAlgHom R A) (invFun R A (p + q)) = p + q
    simp only [invFun_add, AlgHom.map_add, hp, hq]
    -- 🎉 no goals
  · intro n a
    -- ⊢ ↑(toFunAlgHom R A) (invFun R A (↑(monomial n) a)) = ↑(monomial n) a
    rw [invFun_monomial, Algebra.TensorProduct.tmul_pow,
        one_pow, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul, toFunAlgHom_apply_tmul,
        X_pow_eq_monomial, sum_monomial_index] <;>
      simp
      -- 🎉 no goals
      -- 🎉 no goals
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

open DMatrix Matrix BigOperators

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

open Finset

theorem matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
    matPolyEquiv (stdBasisMatrix i j <| monomial k x) = monomial k (stdBasisMatrix i j x) := by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_std_basis]
  -- ⊢ ↑(AlgEquiv.symm (polyEquivTensor R (Matrix n n R))) (↑(Algebra.TensorProduct …
  apply (polyEquivTensor R (Matrix n n R)).injective
  -- ⊢ ↑(polyEquivTensor R (Matrix n n R)) (↑(AlgEquiv.symm (polyEquivTensor R (Mat …
  simp only [AlgEquiv.apply_symm_apply,Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [Algebra.TensorProduct.tmul_mul_tmul, one_pow, one_mul, Matrix.mul_one,
    Algebra.TensorProduct.tmul_pow, Algebra.TensorProduct.includeLeft_apply]
  rw [← smul_X_eq_monomial, ← TensorProduct.smul_tmul]
  -- ⊢ (x • stdBasisMatrix i j 1) ⊗ₜ[R] (X ^ k) = ↑↑includeLeft (stdBasisMatrix i j …
  congr with i' <;> simp [stdBasisMatrix]
  -- ⊢ (x • stdBasisMatrix i j 1) i' x✝ = ↑(LinearMap.mulLeft R (stdBasisMatrix i j …
                    -- 🎉 no goals
                    -- 🎉 no goals
#align mat_poly_equiv_coeff_apply_aux_1 matPolyEquiv_coeff_apply_aux_1

theorem matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : ℕ) :
    coeff (matPolyEquiv (stdBasisMatrix i j p)) k = stdBasisMatrix i j (coeff p k) := by
  refine Polynomial.induction_on' p ?_ ?_
  -- ⊢ ∀ (p q : R[X]), coeff (↑matPolyEquiv (stdBasisMatrix i j p)) k = stdBasisMat …
  · intro p q hp hq
    -- ⊢ coeff (↑matPolyEquiv (stdBasisMatrix i j (p + q))) k = stdBasisMatrix i j (c …
    ext
    -- ⊢ coeff (↑matPolyEquiv (stdBasisMatrix i j (p + q))) k i✝ x✝ = stdBasisMatrix  …
    simp [hp, hq, coeff_add, DMatrix.add_apply, stdBasisMatrix_add]
    -- 🎉 no goals
  · intro k x
    -- ⊢ coeff (↑matPolyEquiv (stdBasisMatrix i j (↑(monomial k) x))) k✝ = stdBasisMa …
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    -- ⊢ (if k = k✝ then stdBasisMatrix i j x else 0) = stdBasisMatrix i j (if k = k✝ …
    split_ifs <;>
    -- ⊢ stdBasisMatrix i j x = stdBasisMatrix i j x
      · funext
        -- ⊢ stdBasisMatrix i j x x✝¹ x✝ = stdBasisMatrix i j x x✝¹ x✝
        -- ⊢ OfNat.ofNat 0 x✝¹ x✝ = stdBasisMatrix i j 0 x✝¹ x✝
        -- 🎉 no goals
        simp
        -- 🎉 no goals
#align mat_poly_equiv_coeff_apply_aux_2 matPolyEquiv_coeff_apply_aux_2

@[simp]
theorem matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : ℕ) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k := by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
    -- 🎉 no goals
  · intro p q hp hq
    -- ⊢ coeff (↑matPolyEquiv (p + q)) k i j = coeff ((p + q) i j) k
    simp [hp, hq]
    -- 🎉 no goals
  · intro i' j' x
    -- ⊢ coeff (↑matPolyEquiv (stdBasisMatrix i' j' x)) k i j = coeff (stdBasisMatrix …
    erw [matPolyEquiv_coeff_apply_aux_2]
    -- ⊢ stdBasisMatrix i' j' (coeff x k) i j = coeff (stdBasisMatrix i' j' x i j) k
    dsimp [stdBasisMatrix]
    -- ⊢ (if i' = i ∧ j' = j then coeff x k else 0) = coeff (if i' = i ∧ j' = j then  …
    split_ifs <;> rename_i h
    -- ⊢ coeff x k = coeff x k
                  -- ⊢ coeff x k = coeff x k
                  -- ⊢ 0 = coeff 0 k
    · rcases h with ⟨rfl, rfl⟩
      -- ⊢ coeff x k = coeff x k
      simp [stdBasisMatrix]
      -- 🎉 no goals
    · simp [stdBasisMatrix, h]
      -- 🎉 no goals
#align mat_poly_equiv_coeff_apply matPolyEquiv_coeff_apply

@[simp]
theorem matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : ℕ) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j := by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  -- ⊢ coeff (↑(AlgEquiv.symm matPolyEquiv) p i j) k = coeff p k i j
  conv_rhs => rw [t]
  -- ⊢ coeff (↑(AlgEquiv.symm matPolyEquiv) p i j) k = coeff (↑matPolyEquiv (↑(AlgE …
  simp only [matPolyEquiv_coeff_apply]
  -- 🎉 no goals
#align mat_poly_equiv_symm_apply_coeff matPolyEquiv_symm_apply_coeff

theorem matPolyEquiv_smul_one (p : R[X]) :
    matPolyEquiv (p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R)) := by
  ext m i j
  -- ⊢ coeff (↑matPolyEquiv (p • 1)) m i j = coeff (Polynomial.map (algebraMap R (M …
  simp only [coeff_map, one_apply, algebraMap_matrix_apply, mul_boole, Pi.smul_apply,
    matPolyEquiv_coeff_apply]
  split_ifs <;> simp <;> rename_i h <;> simp [h]
  -- ⊢ coeff ((p • 1) i j) m = ↑(algebraMap R R) (coeff p m)
                -- ⊢ coeff (p * OfNat.ofNat 1 i j) m = coeff p m
                -- ⊢ coeff (p * OfNat.ofNat 1 i j) m = 0
                         -- ⊢ coeff (p * OfNat.ofNat 1 i j) m = coeff p m
                         -- ⊢ coeff (p * OfNat.ofNat 1 i j) m = 0
                                        -- 🎉 no goals
                                        -- 🎉 no goals
#align mat_poly_equiv_smul_one matPolyEquiv_smul_one

theorem support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) ⊆ support (matPolyEquiv m) := by
  intro k
  -- ⊢ k ∈ support (m i j) → k ∈ support (↑matPolyEquiv m)
  contrapose
  -- ⊢ ¬k ∈ support (↑matPolyEquiv m) → ¬k ∈ support (m i j)
  simp only [not_mem_support_iff]
  -- ⊢ coeff (↑matPolyEquiv m) k = 0 → coeff (m i j) k = 0
  intro hk
  -- ⊢ coeff (m i j) k = 0
  rw [← matPolyEquiv_coeff_apply, hk]
  -- ⊢ OfNat.ofNat 0 i j = 0
  rfl
  -- 🎉 no goals
#align support_subset_support_mat_poly_equiv support_subset_support_matPolyEquiv

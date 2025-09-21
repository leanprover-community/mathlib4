/-
Copyright (c) 2020 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Composition
import Mathlib.RingTheory.MatrixAlgebra
import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

We obtain the algebra isomorphism
```
def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X]
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

open Matrix

variable {R}
variable {n : Type w} [DecidableEq n] [Fintype n]

/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`matPolyEquiv_coeff_apply` below.)
-/
noncomputable def matPolyEquiv : Matrix n n R[X] ≃ₐ[R] (Matrix n n R)[X] :=
  ((matrixEquivTensor n R R[X]).trans (Algebra.TensorProduct.comm R _ _)).trans
    (polyEquivTensor R (Matrix n n R)).symm

@[simp] theorem matPolyEquiv_symm_C (M : Matrix n n R) : matPolyEquiv.symm (C M) = M.map C := by
  simp [matPolyEquiv]

@[simp] theorem matPolyEquiv_map_C (M : Matrix n n R) : matPolyEquiv (M.map C) = C M := by
  rw [← matPolyEquiv_symm_C, AlgEquiv.apply_symm_apply]

@[simp] theorem matPolyEquiv_symm_X :
    matPolyEquiv.symm X = diagonal fun _ : n => (X : R[X]) := by
  simp [matPolyEquiv, Matrix.smul_one_eq_diagonal]

@[simp] theorem matPolyEquiv_diagonal_X :
    matPolyEquiv (diagonal fun _ : n => (X : R[X])) = X := by
  rw [← matPolyEquiv_symm_X, AlgEquiv.apply_symm_apply]

open Finset

unseal Algebra.TensorProduct.mul in
theorem matPolyEquiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
    matPolyEquiv (single i j <| monomial k x) = monomial k (single i j x) := by
  simp only [matPolyEquiv, AlgEquiv.trans_apply, matrixEquivTensor_apply_single]
  apply (polyEquivTensor R (Matrix n n R)).injective
  simp only [AlgEquiv.apply_symm_apply,Algebra.TensorProduct.comm_tmul,
    polyEquivTensor_apply, eval₂_monomial]
  simp only [one_pow,
    Algebra.TensorProduct.tmul_pow]
  rw [← smul_X_eq_monomial, ← TensorProduct.smul_tmul]
  congr with i' <;> simp [single]

theorem matPolyEquiv_coeff_apply_aux_2 (i j : n) (p : R[X]) (k : ℕ) :
    coeff (matPolyEquiv (single i j p)) k = single i j (coeff p k) := by
  refine Polynomial.induction_on' p ?_ ?_
  · intro p q hp hq
    ext
    simp [hp, hq, coeff_add, add_apply, single_add]
  · intro k x
    simp only [matPolyEquiv_coeff_apply_aux_1, coeff_monomial]
    split_ifs <;>
      · funext
        simp

@[simp]
theorem matPolyEquiv_coeff_apply (m : Matrix n n R[X]) (k : ℕ) (i j : n) :
    coeff (matPolyEquiv m) k i j = coeff (m i j) k := by
  refine Matrix.induction_on' m ?_ ?_ ?_
  · simp
  · intro p q hp hq
    simp [hp, hq]
  · intro i' j' x
    rw [matPolyEquiv_coeff_apply_aux_2]
    dsimp [single]
    split_ifs <;> rename_i h
    · constructor
    · simp

@[simp]
theorem matPolyEquiv_symm_apply_coeff (p : (Matrix n n R)[X]) (i j : n) (k : ℕ) :
    coeff (matPolyEquiv.symm p i j) k = coeff p k i j := by
  have t : p = matPolyEquiv (matPolyEquiv.symm p) := by simp
  conv_rhs => rw [t]
  simp only [matPolyEquiv_coeff_apply]

theorem matPolyEquiv_smul_one (p : R[X]) :
    matPolyEquiv (p • (1 : Matrix n n R[X])) = p.map (algebraMap R (Matrix n n R)) := by
  ext m i j
  simp only [matPolyEquiv_coeff_apply, smul_apply, one_apply, smul_eq_mul, mul_ite, mul_one,
    mul_zero, coeff_map, algebraMap_matrix_apply, Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs <;> simp

@[simp]
lemma matPolyEquiv_map_smul (p : R[X]) (M : Matrix n n R[X]) :
    matPolyEquiv (p • M) = p.map (algebraMap _ _) * matPolyEquiv M := by
  rw [← one_mul M, ← smul_mul_assoc, map_mul, matPolyEquiv_smul_one, one_mul]

theorem support_subset_support_matPolyEquiv (m : Matrix n n R[X]) (i j : n) :
    support (m i j) ⊆ support (matPolyEquiv m) := by
  intro k
  contrapose
  simp only [notMem_support_iff]
  intro hk
  rw [← matPolyEquiv_coeff_apply, hk, zero_apply]

variable {A}
/-- Extend a ring hom `A → Mₙ(R)` to a ring hom `A[X] → Mₙ(R[X])`. -/
def RingHom.polyToMatrix (f : A →+* Matrix n n R) : A[X] →+* Matrix n n R[X] :=
  matPolyEquiv.symm.toRingHom.comp (mapRingHom f)

variable {S : Type*} [CommSemiring S] (f : S →+* Matrix n n R)

lemma evalRingHom_mapMatrix_comp_polyToMatrix :
    (evalRingHom 0).mapMatrix.comp f.polyToMatrix = f.comp (evalRingHom 0) := by
  ext <;> simp [RingHom.polyToMatrix, - AlgEquiv.symm_toRingEquiv, diagonal, apply_ite]

lemma evalRingHom_mapMatrix_comp_compRingEquiv {m} [Fintype m] [DecidableEq m] :
    (evalRingHom 0).mapMatrix.comp (compRingEquiv m n R[X]) =
      (compRingEquiv m n R).toRingHom.comp (evalRingHom 0).mapMatrix.mapMatrix := by
  ext; simp

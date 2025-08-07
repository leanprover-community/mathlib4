/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Changing the index type of a matrix

This file concerns the map `Matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `Matrix.reindexLinearEquiv R A`: `Matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `Matrix.reindexAlgEquiv R`: `Matrix.reindex` is an `R`-algebra equivalence between `R`-matrices.

## Tags

matrix, reindex

-/


namespace Matrix

open Equiv Matrix

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}
variable (R A : Type*)

section AddCommMonoid

variable [Semiring R] [AddCommMonoid A] [Module R A]

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is a linear equivalence. -/
def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A :=
  { reindex eₘ eₙ with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp]
theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M :=
  rfl

@[simp]
theorem reindexLinearEquiv_symm (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl

@[simp]
theorem reindexLinearEquiv_refl_refl :
    reindexLinearEquiv R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => rfl

theorem reindexLinearEquiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) := by
  ext
  rfl

theorem reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') := by
  rw [← reindexLinearEquiv_trans]
  rfl

theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  submatrix_submatrix _ _ _ _ _

theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 :=
  submatrix_one_equiv e.symm

end AddCommMonoid

section Semiring

variable [Semiring R] [Semiring A] [Module R A]

theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M * reindexLinearEquiv R A eₙ eₒ N =
      reindexLinearEquiv R A eₘ eₒ (M * N) :=
  submatrix_mul_equiv M N _ _ _

theorem mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M * (reindexLinearEquiv R A e₁ e₂ 1) =
      reindexLinearEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M :=
  haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _

end Semiring

section Algebra

variable [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]
  [Semiring A] [Algebra R A]

/-- For square matrices with coefficients in an algebra over a commutative semiring, the natural
map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is an equivalence of algebras. -/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m A ≃ₐ[R] Matrix n n A :=
  { reindexLinearEquiv A A e e with
    toFun := reindex e e
    map_mul' := fun a b => (reindexLinearEquiv_mul A A e e e a b).symm
    commutes' := fun r => by simp [algebraMap, Algebra.algebraMap] }

@[simp]
theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexAlgEquiv R A e M = reindex e e M :=
  rfl

@[simp]
theorem reindexAlgEquiv_symm (e : m ≃ n) : (reindexAlgEquiv R A e).symm =
    reindexAlgEquiv R A e.symm :=
  rfl

@[simp]
theorem reindexAlgEquiv_refl : reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl

theorem reindexAlgEquiv_mul (e : m ≃ n) (M : Matrix m m A) (N : Matrix m m A) :
    reindexAlgEquiv R A e (M * N) = reindexAlgEquiv R A e M * reindexAlgEquiv R A e N :=
  map_mul ..

end Algebra

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexLinearEquiv_self [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) : det (reindexLinearEquiv R R e e M) = det M :=
  det_reindex_self e M

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexAlgEquiv (B : Type*) [CommSemiring R] [CommRing B] [Algebra R B] [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (e : m ≃ n) (A : Matrix m m B) :
    det (reindexAlgEquiv R B e A) = det A :=
  det_reindex_self e A

end Matrix

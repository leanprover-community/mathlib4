/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

#align_import linear_algebra.matrix.reindex from "leanprover-community/mathlib"@"1cfdf5f34e1044ecb65d10be753008baaf118edf"

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
#align matrix.reindex_linear_equiv Matrix.reindexLinearEquiv

@[simp]
theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M :=
  rfl
#align matrix.reindex_linear_equiv_apply Matrix.reindexLinearEquiv_apply

@[simp]
theorem reindexLinearEquiv_symm (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl
#align matrix.reindex_linear_equiv_symm Matrix.reindexLinearEquiv_symm

@[simp]
theorem reindexLinearEquiv_refl_refl :
    reindexLinearEquiv R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R _ :=
  LinearEquiv.ext fun _ => rfl
#align matrix.reindex_linear_equiv_refl_refl Matrix.reindexLinearEquiv_refl_refl

theorem reindexLinearEquiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) := by
  ext
  rfl
#align matrix.reindex_linear_equiv_trans Matrix.reindexLinearEquiv_trans

theorem reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') := by
  rw [← reindexLinearEquiv_trans]
  rfl
#align matrix.reindex_linear_equiv_comp Matrix.reindexLinearEquiv_comp

theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  submatrix_submatrix _ _ _ _ _
#align matrix.reindex_linear_equiv_comp_apply Matrix.reindexLinearEquiv_comp_apply

theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 :=
  submatrix_one_equiv e.symm
#align matrix.reindex_linear_equiv_one Matrix.reindexLinearEquiv_one

end AddCommMonoid

section Semiring

variable [Semiring R] [Semiring A] [Module R A]

theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M * reindexLinearEquiv R A eₙ eₒ N =
      reindexLinearEquiv R A eₘ eₒ (M * N) :=
  submatrix_mul_equiv M N _ _ _
#align matrix.reindex_linear_equiv_mul Matrix.reindexLinearEquiv_mul

theorem mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M * (reindexLinearEquiv R A e₁ e₂ 1) =
      reindexLinearEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M :=
  haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _
#align matrix.mul_reindex_linear_equiv_one Matrix.mul_reindexLinearEquiv_one

end Semiring

section Algebra

variable [CommSemiring R] [Fintype n] [Fintype m] [DecidableEq m] [DecidableEq n]

/-- For square matrices with coefficients in commutative semirings, the natural map that reindexes
a matrix's rows and columns with equivalent types, `Matrix.reindex`, is an equivalence of algebras.
-/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m R ≃ₐ[R] Matrix n n R :=
  { reindexLinearEquiv R R e e with
    toFun := reindex e e
    map_mul' := fun a b => (reindexLinearEquiv_mul R R e e e a b).symm
    -- Porting note: `submatrix_smul` needed help
    commutes' := fun r => by simp [algebraMap, Algebra.toRingHom, submatrix_smul _ 1] }
#align matrix.reindex_alg_equiv Matrix.reindexAlgEquiv

@[simp]
theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m R) :
    reindexAlgEquiv R e M = reindex e e M :=
  rfl
#align matrix.reindex_alg_equiv_apply Matrix.reindexAlgEquiv_apply

@[simp]
theorem reindexAlgEquiv_symm (e : m ≃ n) : (reindexAlgEquiv R e).symm = reindexAlgEquiv R e.symm :=
  rfl
#align matrix.reindex_alg_equiv_symm Matrix.reindexAlgEquiv_symm

@[simp]
theorem reindexAlgEquiv_refl : reindexAlgEquiv R (Equiv.refl m) = AlgEquiv.refl :=
  AlgEquiv.ext fun _ => rfl
#align matrix.reindex_alg_equiv_refl Matrix.reindexAlgEquiv_refl

theorem reindexAlgEquiv_mul (e : m ≃ n) (M : Matrix m m R) (N : Matrix m m R) :
    reindexAlgEquiv R e (M * N) = reindexAlgEquiv R e M * reindexAlgEquiv R e N :=
  (reindexAlgEquiv R e).map_mul M N
#align matrix.reindex_alg_equiv_mul Matrix.reindexAlgEquiv_mul

end Algebra

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexLinearEquiv_self [CommRing R] [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) : det (reindexLinearEquiv R R e e M) = det M :=
  det_reindex_self e M
#align matrix.det_reindex_linear_equiv_self Matrix.det_reindexLinearEquiv_self

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_submatrix_equiv_self`.
-/
theorem det_reindexAlgEquiv [CommRing R] [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m R) : det (reindexAlgEquiv R e A) = det A :=
  det_reindex_self e A
#align matrix.det_reindex_alg_equiv Matrix.det_reindexAlgEquiv

end Matrix

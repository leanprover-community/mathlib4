/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Snir Broshi
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Changing the index type of a matrix

This file concerns the map `Matrix.reindex`, mapping a `m` by `n` matrix
to an `m'` by `n'` matrix, as long as `m ≃ m'` and `n ≃ n'`.

## Main definitions

* `Matrix.reindexAddEquiv R`: `Matrix.reindex` as an `AddEquiv` between `R`-matrices.
* `Matrix.reindexRingEquiv R`: `Matrix.reindex` as a `RingEquiv` between `R`-matrices.
* `Matrix.reindexLinearEquiv R A`: `Matrix.reindex` is an `R`-linear equivalence between
  `A`-matrices.
* `Matrix.reindexAlgEquiv R A`: `Matrix.reindex` is an `R`-algebra equivalence between `A`-matrices.

## Tags

matrix, reindex

-/

@[expose] public section


namespace Matrix

open Equiv Matrix

variable {l m n o : Type*} {l' m' n' o' : Type*} {m'' n'' : Type*}
variable (R A : Type*)

section Add

variable [Add R]

/-- `Matrix.reindex` as an `AddEquiv` between `R`-matrices. -/
def reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n R ≃+ Matrix m' n' R where
  __ := reindex eₘ eₙ
  map_add' _ _ := rfl

@[simp]
theorem coe_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    ⇑(reindexAddEquiv R eₘ eₙ) = reindex eₘ eₙ :=
  rfl

@[simp]
theorem toEquiv_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexAddEquiv R eₘ eₙ : Matrix m n R ≃ Matrix m' n' R) = reindex eₘ eₙ :=
  rfl

@[simp]
theorem symm_reindexAddEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexAddEquiv R eₘ eₙ).symm = reindexAddEquiv R eₘ.symm eₙ.symm :=
  rfl

@[simp]
theorem reindexAddEquiv_refl_refl : reindexAddEquiv R (.refl m) (.refl n) = .refl _ :=
  rfl

@[simp]
theorem reindexAddEquiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    .trans (reindexAddEquiv R e₁ e₂) (reindexAddEquiv R e₁' e₂') =
      reindexAddEquiv R (.trans e₁ e₁') (.trans e₂ e₂') :=
  rfl

end Add

section Mul

variable [Fintype m] [Fintype n] [Fintype o] [Mul R] [AddCommMonoid R]

/-- `Matrix.reindex` as a `RingEquiv` between `R`-matrices. -/
def reindexRingEquiv (e : m ≃ n) : Matrix m m R ≃+* Matrix n n R where
  __ := reindexAddEquiv R e e
  map_mul' A B := submatrix_mul_equiv A B .. |>.symm

@[simp]
theorem coe_reindexRingEquiv (e : m ≃ n) : ⇑(reindexRingEquiv R e) = reindex e e :=
  rfl

@[simp]
theorem toEquiv_reindexRingEquiv (e : m ≃ n) :
    (reindexRingEquiv R e : Matrix m m R ≃ Matrix n n R) = reindex e e :=
  rfl

@[simp]
theorem toAddEquiv_reindexRingEquiv (e : m ≃ n) : reindexRingEquiv R e = reindexAddEquiv R e e :=
  rfl

@[simp]
theorem symm_reindexRingEquiv (e : m ≃ n) :
    (reindexRingEquiv R e).symm = reindexRingEquiv R e.symm :=
  rfl

@[simp]
theorem reindexRingEquiv_refl_refl : reindexRingEquiv R (.refl n) = .refl _ :=
  rfl

@[simp]
theorem reindexRingEquiv_trans (e : m ≃ n) (e' : n ≃ o) :
    .trans (reindexRingEquiv R e) (reindexRingEquiv R e') = reindexRingEquiv R (.trans e e') :=
  rfl

end Mul

section AddCommMonoid

variable [Semiring R] [AddCommMonoid A] [Module R A]

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is a linear equivalence. -/
def reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') : Matrix m n A ≃ₗ[R] Matrix m' n' A where
  __ := reindexAddEquiv A eₘ eₙ
  map_smul' _ _ := rfl

@[simp]
theorem coe_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    ⇑(reindexLinearEquiv R A eₘ eₙ) = reindex eₘ eₙ :=
  rfl

@[simp]
theorem toEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ : Matrix m n A ≃ Matrix m' n' A) = reindex eₘ eₙ :=
  rfl

@[simp]
theorem toAddEquiv_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    reindexLinearEquiv R A eₘ eₙ = reindexAddEquiv A eₘ eₙ :=
  rfl

@[deprecated "Use `by simp` instead." (since := "2026-05-13")]
theorem reindexLinearEquiv_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : Matrix m n A) :
    reindexLinearEquiv R A eₘ eₙ M = reindex eₘ eₙ M := by
  simp

@[simp]
theorem symm_reindexLinearEquiv (eₘ : m ≃ m') (eₙ : n ≃ n') :
    (reindexLinearEquiv R A eₘ eₙ).symm = reindexLinearEquiv R A eₘ.symm eₙ.symm :=
  rfl

@[deprecated (since := "2026-05-15")] alias reindexLinearEquiv_symm := symm_reindexLinearEquiv

@[simp]
theorem reindexLinearEquiv_refl_refl :
    reindexLinearEquiv R A (Equiv.refl m) (Equiv.refl n) = LinearEquiv.refl R _ :=
  rfl

@[simp]
theorem reindexLinearEquiv_trans (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    (reindexLinearEquiv R A e₁ e₂).trans (reindexLinearEquiv R A e₁' e₂') =
      (reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') : _ ≃ₗ[R] _) :=
  rfl

theorem reindexLinearEquiv_comp (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'') :
    reindexLinearEquiv R A e₁' e₂' ∘ reindexLinearEquiv R A e₁ e₂ =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') :=
  rfl

theorem reindexLinearEquiv_comp_apply (e₁ : m ≃ m') (e₂ : n ≃ n') (e₁' : m' ≃ m'') (e₂' : n' ≃ n'')
    (M : Matrix m n A) :
    (reindexLinearEquiv R A e₁' e₂') (reindexLinearEquiv R A e₁ e₂ M) =
      reindexLinearEquiv R A (e₁.trans e₁') (e₂.trans e₂') M :=
  rfl

theorem reindexLinearEquiv_one [DecidableEq m] [DecidableEq m'] [One A] (e : m ≃ m') :
    reindexLinearEquiv R A e e (1 : Matrix m m A) = 1 := by
  simp

end AddCommMonoid

section Semiring

variable [Semiring R] [Semiring A] [Module R A]

theorem reindexLinearEquiv_mul [Fintype n] [Fintype n'] (eₘ : m ≃ m') (eₙ : n ≃ n') (eₒ : o ≃ o')
    (M : Matrix m n A) (N : Matrix n o A) :
    reindexLinearEquiv R A eₘ eₙ M * reindexLinearEquiv R A eₙ eₒ N =
      reindexLinearEquiv R A eₘ eₒ (M * N) := by
  simp

theorem mul_reindexLinearEquiv_one [Fintype n] [DecidableEq o] (e₁ : o ≃ n) (e₂ : o ≃ n')
    (M : Matrix m n A) :
    M * (reindexLinearEquiv R A e₁ e₂ 1) =
      reindexLinearEquiv R A (Equiv.refl m) (e₁.symm.trans e₂) M :=
  haveI := Fintype.ofEquiv _ e₁.symm
  mul_submatrix_one _ _ _

end Semiring

section Algebra

variable [CommSemiring R] [Fintype n] [Fintype m] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o] [Semiring A] [Algebra R A]

/-- For square matrices with coefficients in an algebra over a commutative semiring, the natural
map that reindexes a matrix's rows and columns with equivalent types,
`Matrix.reindex`, is an equivalence of algebras. -/
def reindexAlgEquiv (e : m ≃ n) : Matrix m m A ≃ₐ[R] Matrix n n A where
  __ := reindexRingEquiv A e
  commutes' _ := by simp [algebraMap]

@[simp]
theorem coe_reindexAlgEquiv (e : m ≃ n) : ⇑(reindexAlgEquiv R A e) = reindex e e :=
  rfl

@[simp]
theorem toEquiv_reindexAlgEquiv (e : m ≃ n) :
    (reindexAlgEquiv R A e : Matrix m m A ≃ Matrix n n A) = reindex e e :=
  rfl

@[simp]
theorem toAddEquiv_reindexAlgEquiv (e : m ≃ n) : reindexAlgEquiv R A e = reindexAddEquiv A e e :=
  rfl

@[simp]
theorem toLinearEquiv_reindexAlgEquiv (e : m ≃ n) :
    reindexAlgEquiv R A e = reindexLinearEquiv R A e e :=
  rfl

@[deprecated "Use `by simp` instead." (since := "2026-05-13")]
theorem reindexAlgEquiv_apply (e : m ≃ n) (M : Matrix m m A) :
    reindexAlgEquiv R A e M = reindex e e M := by
  simp

@[simp]
theorem symm_reindexAlgEquiv (e : m ≃ n) : (reindexAlgEquiv R A e).symm =
    reindexAlgEquiv R A e.symm :=
  rfl

@[deprecated (since := "2026-05-15")] alias reindexAlgEquiv_symm := symm_reindexAlgEquiv

@[simp]
theorem reindexAlgEquiv_refl : reindexAlgEquiv R A (Equiv.refl m) = AlgEquiv.refl :=
  rfl

@[simp]
theorem reindexAlgEquiv_trans (e : m ≃ n) (e' : n ≃ o) :
    .trans (reindexAlgEquiv R A e) (reindexAlgEquiv R A e') = reindexAlgEquiv R A (.trans e e') :=
  rfl

@[deprecated map_mul (since := "2026-05-13")]
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

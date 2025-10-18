/-
Copyright (c) 2023 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Data.Finsupp.Fin

/-!
# `Finsupp.sum` and `Finsupp.prod` over `Fin`

This file contains theorems relevant to big operators on finitely supported functions over `Fin`.
-/

namespace Finsupp

variable {M N : Type*}

lemma sum_cons [AddCommMonoid M] (n : ℕ) (σ : Fin n →₀ M) (i : M) :
    (sum (cons i σ) fun _ e ↦ e) = i + sum σ (fun _ e ↦ e) := by
  rw [sum_fintype _ _ (fun _ => rfl), sum_fintype _ _ (fun _ => rfl)]
  exact Fin.sum_cons i σ

lemma sum_cons' [Zero M] [AddCommMonoid N] (n : ℕ) (σ : Fin n →₀ M) (i : M)
    (f : Fin (n + 1) → M → N) (h : ∀ x, f x 0 = 0) :
    (sum (Finsupp.cons i σ) f) = f 0 i + sum σ (Fin.tail f) := by
  rw [sum_fintype _ _ (fun _ => by apply h), sum_fintype _ _ (fun _ => by apply h)]
  simp_rw [Fin.sum_univ_succ, cons_zero, cons_succ]
  congr

theorem ofSupportFinite_fin_two_eq (n : Fin 2 →₀ ℕ) :
    ofSupportFinite ![n 0, n 1] (Set.toFinite _) = n := by
  rw [Finsupp.ext_iff, Fin.forall_fin_two]
  exact ⟨rfl, rfl⟩

end Finsupp

section Fin2

variable (X : Type*) [Zero X]

/-- The space of finitely supported functions `Fin 2 →₀ α` is equivalent to `α × α`.
See also `finTwoArrowEquiv`. -/
@[simps -fullyApplied]
noncomputable def finTwoArrowEquiv' : (Fin 2 →₀ X) ≃ (X × X) where
  toFun x     := (x 0, x 1)
  invFun x    := Finsupp.ofSupportFinite ![x.1, x.2] (Set.toFinite _)
  left_inv x  := by
    simp only [Fin.isValue, Finsupp.ext_iff, Fin.forall_fin_two]
    exact ⟨rfl, rfl⟩
  right_inv x := rfl

theorem finTwoArrowEquiv'_sum_eq {d : ℕ × ℕ} :
    (((finTwoArrowEquiv' ℕ).symm d).sum fun _ n ↦ n) = d.1 + d.2 := by
  simp [Finsupp.sum, finTwoArrowEquiv'_symm_apply, Finsupp.ofSupportFinite_coe]
  rw [Finset.sum_subset (Finset.subset_univ _)
    (fun _ _ h ↦ by simpa [Finsupp.ofSupportFinite_coe] using h)]
  simp [Fin.sum_univ_two, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_fin_one]

end Fin2

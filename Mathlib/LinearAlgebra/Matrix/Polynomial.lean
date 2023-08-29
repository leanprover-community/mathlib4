/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Data.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant

#align_import linear_algebra.matrix.polynomial from "leanprover-community/mathlib"@"70fd9563a21e7b963887c9360bd29b2393e6225a"

/-!
# Matrices of polynomials and polynomials of matrices

In this file, we prove results about matrices over a polynomial ring.
In particular, we give results about the polynomial given by
`det (t * I + A)`.

## References

  * "The trace Cayley-Hamilton theorem" by Darij Grinberg, Section 5.3

## Tags

matrix determinant, polynomial
-/

set_option linter.uppercaseLean3 false

open Matrix BigOperators Polynomial

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

open Polynomial Matrix Equiv.Perm

namespace Polynomial

theorem natDegree_det_X_add_C_le (A B : Matrix n n α) :
    natDegree (det ((X : α[X]) • A.map C + B.map C)) ≤ Fintype.card n := by
  rw [det_apply]
  -- ⊢ natDegree (∑ σ : Equiv.Perm n, ↑sign σ • ∏ i : n, (X • Matrix.map A ↑C + Mat …
  refine' (natDegree_sum_le _ _).trans _
  -- ⊢ Finset.fold max 0 (natDegree ∘ fun σ => ↑sign σ • ∏ i : n, (X • Matrix.map A …
  refine' Multiset.max_nat_le_of_forall_le _ _ _
  -- ⊢ ∀ (x : ℕ), x ∈ Multiset.map (natDegree ∘ fun σ => ↑sign σ • ∏ i : n, (X • Ma …
  simp only [forall_apply_eq_imp_iff', true_and_iff, Function.comp_apply, Multiset.map_map,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  -- ⊢ natDegree (↑sign g • ∏ x : n, (X • Matrix.map A ↑C + Matrix.map B ↑C) (↑g x) …
  calc
    natDegree (sign g • ∏ i : n, (X • A.map C + B.map C) (g i) i) ≤
        natDegree (∏ i : n, (X • A.map C + B.map C) (g i) i) := by
      cases' Int.units_eq_one_or (sign g) with sg sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : n, natDegree (((X : α[X]) • A.map C + B.map C) (g i) i) :=
      (natDegree_prod_le (Finset.univ : Finset n) fun i : n => (X • A.map C + B.map C) (g i) i)
    _ ≤ Finset.univ.card • 1 := (Finset.sum_le_card_nsmul _ _ 1 fun (i : n) _ => ?_)
    _ ≤ Fintype.card n := by simp [mul_one, Algebra.id.smul_eq_mul, Finset.card_univ]

  calc
    natDegree (((X : α[X]) • A.map C + B.map C) (g i) i) =
        natDegree ((X : α[X]) * C (A (g i) i) + C (B (g i) i)) :=
      by simp
    _ ≤ max (natDegree ((X : α[X]) * C (A (g i) i))) (natDegree (C (B (g i) i))) :=
      (natDegree_add_le _ _)
    _ = natDegree ((X : α[X]) * C (A (g i) i)) :=
      (max_eq_left ((natDegree_C _).le.trans (zero_le _)))
    _ ≤ natDegree (X : α[X]) := (natDegree_mul_C_le _ _)
    _ ≤ 1 := natDegree_X_le
#align polynomial.nat_degree_det_X_add_C_le Polynomial.natDegree_det_X_add_C_le

theorem coeff_det_X_add_C_zero (A B : Matrix n n α) :
    coeff (det ((X : α[X]) • A.map C + B.map C)) 0 = det B := by
  rw [det_apply, finset_sum_coeff, det_apply]
  -- ⊢ ∑ b : Equiv.Perm n, coeff (↑sign b • ∏ i : n, (X • Matrix.map A ↑C + Matrix. …
  refine' Finset.sum_congr rfl _
  -- ⊢ ∀ (x : Equiv.Perm n), x ∈ Finset.univ → coeff (↑sign x • ∏ i : n, (X • Matri …
  rintro g -
  -- ⊢ coeff (↑sign g • ∏ i : n, (X • Matrix.map A ↑C + Matrix.map B ↑C) (↑g i) i)  …
  convert coeff_smul (R := α) (sign g) _ 0
  -- ⊢ ∏ i : n, B (↑g i) i = coeff (∏ i : n, (X • Matrix.map A ↑C + Matrix.map B ↑C …
  rw [coeff_zero_prod]
  -- ⊢ ∏ i : n, B (↑g i) i = ∏ i : n, coeff ((X • Matrix.map A ↑C + Matrix.map B ↑C …
  refine' Finset.prod_congr rfl _
  -- ⊢ ∀ (x : n), x ∈ Finset.univ → B (↑g x) x = coeff ((X • Matrix.map A ↑C + Matr …
  simp
  -- 🎉 no goals
#align polynomial.coeff_det_X_add_C_zero Polynomial.coeff_det_X_add_C_zero

theorem coeff_det_X_add_C_card (A B : Matrix n n α) :
    coeff (det ((X : α[X]) • A.map C + B.map C)) (Fintype.card n) = det A := by
  rw [det_apply, det_apply, finset_sum_coeff]
  -- ⊢ ∑ b : Equiv.Perm n, coeff (↑sign b • ∏ i : n, (X • Matrix.map A ↑C + Matrix. …
  refine' Finset.sum_congr rfl _
  -- ⊢ ∀ (x : Equiv.Perm n), x ∈ Finset.univ → coeff (↑sign x • ∏ i : n, (X • Matri …
  simp only [Algebra.id.smul_eq_mul, Finset.mem_univ, RingHom.mapMatrix_apply, forall_true_left,
    map_apply, Pi.smul_apply]
  intro g
  -- ⊢ coeff (↑sign g • ∏ x : n, (X • Matrix.map A ↑C + Matrix.map B ↑C) (↑g x) x)  …
  convert coeff_smul (R := α) (sign g) _ _
  -- ⊢ ∏ x : n, A (↑g x) x = coeff (∏ x : n, (X • Matrix.map A ↑C + Matrix.map B ↑C …
  rw [← mul_one (Fintype.card n)]
  -- ⊢ ∏ x : n, A (↑g x) x = coeff (∏ x : n, (X • Matrix.map A ↑C + Matrix.map B ↑C …
  convert (coeff_prod_of_natDegree_le (R := α) _ _ _ _).symm
  -- ⊢ A (↑g x✝) x✝ = coeff ((X • Matrix.map A ↑C + Matrix.map B ↑C) (↑g x✝) x✝) 1
  · simp [coeff_C]
    -- 🎉 no goals
  · rintro p -
    -- ⊢ natDegree ((X • Matrix.map A ↑C + Matrix.map B ↑C) (↑g p) p) ≤ 1
    refine' (natDegree_add_le _ _).trans _
    -- ⊢ max (natDegree ((X • Matrix.map A ↑C) (↑g p) p)) (natDegree (Matrix.map B (↑ …
    simpa [Pi.smul_apply, map_apply, Algebra.id.smul_eq_mul, X_mul_C, natDegree_C,
      max_eq_left, zero_le'] using (natDegree_C_mul_le _ _).trans (natDegree_X_le (R := α))
#align polynomial.coeff_det_X_add_C_card Polynomial.coeff_det_X_add_C_card

theorem leadingCoeff_det_X_one_add_C (A : Matrix n n α) :
    leadingCoeff (det ((X : α[X]) • (1 : Matrix n n α[X]) + A.map C)) = 1 := by
  cases subsingleton_or_nontrivial α
  -- ⊢ leadingCoeff (det (X • 1 + Matrix.map A ↑C)) = 1
  · simp
    -- 🎉 no goals
  rw [← @det_one n, ← coeff_det_X_add_C_card _ A, leadingCoeff]
  -- ⊢ coeff (det (X • 1 + Matrix.map A ↑C)) (natDegree (det (X • 1 + Matrix.map A  …
  simp only [Matrix.map_one, C_eq_zero, RingHom.map_one]
  -- ⊢ coeff (det (X • 1 + Matrix.map A ↑C)) (natDegree (det (X • 1 + Matrix.map A  …
  cases' (natDegree_det_X_add_C_le 1 A).eq_or_lt with h h
  -- ⊢ coeff (det (X • 1 + Matrix.map A ↑C)) (natDegree (det (X • 1 + Matrix.map A  …
  · simp only [RingHom.map_one, Matrix.map_one, C_eq_zero] at h
    -- ⊢ coeff (det (X • 1 + Matrix.map A ↑C)) (natDegree (det (X • 1 + Matrix.map A  …
    rw [h]
    -- 🎉 no goals
  · -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_natDegree_lt h
    -- ⊢ coeff (det (X • 1 + Matrix.map A ↑C)) (natDegree (det (X • 1 + Matrix.map A  …
    rw [coeff_det_X_add_C_card] at H
    -- ⊢ coeff (det (X • 1 + Matrix.map A ↑C)) (natDegree (det (X • 1 + Matrix.map A  …
    simp at H
    -- 🎉 no goals
#align polynomial.leading_coeff_det_X_one_add_C Polynomial.leadingCoeff_det_X_one_add_C

end Polynomial

/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.ComputeDegree

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

open Matrix Polynomial

variable {n α : Type*} [DecidableEq n] [Fintype n] [CommRing α]

open Polynomial Matrix Equiv.Perm

namespace Polynomial

theorem natDegree_det_X_add_C_le (A B : Matrix n n α) :
    natDegree (det ((X : α[X]) • A.map C + B.map C : Matrix n n α[X])) ≤ Fintype.card n := by
  rw [det_apply]
  refine (natDegree_sum_le _ _).trans ?_
  refine Multiset.max_le_of_forall_le _ _ ?_
  simp only [forall_apply_eq_imp_iff, true_and_iff, Function.comp_apply, Multiset.map_map,
    Multiset.mem_map, exists_imp, Finset.mem_univ_val]
  intro g
  calc
    natDegree (sign g • ∏ i : n, (X • A.map C + B.map C : Matrix n n α[X]) (g i) i) ≤
        natDegree (∏ i : n, (X • A.map C + B.map C : Matrix n n α[X]) (g i) i) := by
      cases' Int.units_eq_one_or (sign g) with sg sg
      · rw [sg, one_smul]
      · rw [sg, Units.neg_smul, one_smul, natDegree_neg]
    _ ≤ ∑ i : n, natDegree (((X : α[X]) • A.map C + B.map C : Matrix n n α[X]) (g i) i) :=
      (natDegree_prod_le (Finset.univ : Finset n) fun i : n =>
        (X • A.map C + B.map C : Matrix n n α[X]) (g i) i)
    _ ≤ Finset.univ.card • 1 := (Finset.sum_le_card_nsmul _ _ 1 fun (i : n) _ => ?_)
    _ ≤ Fintype.card n := by simp [mul_one, Algebra.id.smul_eq_mul, Finset.card_univ]
  dsimp only [add_apply, smul_apply, map_apply, smul_eq_mul]
  compute_degree
#align polynomial.nat_degree_det_X_add_C_le Polynomial.natDegree_det_X_add_C_le

theorem coeff_det_X_add_C_zero (A B : Matrix n n α) :
    coeff (det ((X : α[X]) • A.map C + B.map C)) 0 = det B := by
  rw [det_apply, finset_sum_coeff, det_apply]
  refine Finset.sum_congr rfl ?_
  rintro g -
  convert coeff_smul (R := α) (sign g) _ 0
  rw [coeff_zero_prod]
  refine Finset.prod_congr rfl ?_
  simp
#align polynomial.coeff_det_X_add_C_zero Polynomial.coeff_det_X_add_C_zero

theorem coeff_det_X_add_C_card (A B : Matrix n n α) :
    coeff (det ((X : α[X]) • A.map C + B.map C)) (Fintype.card n) = det A := by
  rw [det_apply, det_apply, finset_sum_coeff]
  refine Finset.sum_congr rfl ?_
  simp only [Algebra.id.smul_eq_mul, Finset.mem_univ, RingHom.mapMatrix_apply, forall_true_left,
    map_apply, Pi.smul_apply]
  intro g
  convert coeff_smul (R := α) (sign g) _ _
  rw [← mul_one (Fintype.card n)]
  convert (coeff_prod_of_natDegree_le (R := α) _ _ _ _).symm
  · simp [coeff_C]
  · rintro p -
    dsimp only [add_apply, smul_apply, map_apply, smul_eq_mul]
    compute_degree
#align polynomial.coeff_det_X_add_C_card Polynomial.coeff_det_X_add_C_card

theorem leadingCoeff_det_X_one_add_C (A : Matrix n n α) :
    leadingCoeff (det ((X : α[X]) • (1 : Matrix n n α[X]) + A.map C)) = 1 := by
  cases subsingleton_or_nontrivial α
  · simp [eq_iff_true_of_subsingleton]
  rw [← @det_one n, ← coeff_det_X_add_C_card _ A, leadingCoeff]
  simp only [Matrix.map_one, C_eq_zero, RingHom.map_one]
  rcases (natDegree_det_X_add_C_le 1 A).eq_or_lt with h | h
  · simp only [RingHom.map_one, Matrix.map_one, C_eq_zero] at h
    rw [h]
  · -- contradiction. we have a hypothesis that the degree is less than |n|
    -- but we know that coeff _ n = 1
    have H := coeff_eq_zero_of_natDegree_lt h
    rw [coeff_det_X_add_C_card] at H
    simp at H
#align polynomial.leading_coeff_det_X_one_add_C Polynomial.leadingCoeff_det_X_one_add_C

end Polynomial

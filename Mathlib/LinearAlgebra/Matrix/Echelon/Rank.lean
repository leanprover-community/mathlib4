/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.List.Sort
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Rank from a pivot of a row echelon form

A *pivot* of a matrix lists the leading (leftmost nonzero) columns of the nonzero rows of a
matrix in row echelon form. Its length is the rank of the matrix, which lets the rank be read
off a `T * (P * M)` decomposition (`T` lower triangular with nonzero diagonal, `P` a row
permutation) without materialising the product.

## Main definitions

- `Matrix.IsPivot`: `l` is a pivot of `A`.

## Main results

- `Matrix.IsPivot.rank_eq`: a matrix with pivot `l` has rank `l.length`.
- `Matrix.IsPivot.rowEchelon`: a matrix with a pivot is in row echelon form.
- `Matrix.rank_mul_eq_right_of_lowerTriangular`: multiplying by a lower triangular matrix with
  nonzero diagonal and a row permutation does not change the rank.
- `Matrix.IsPivot.rank_eq_of_lowerTriangular`: the rank of `B`, read off a pivot of
  `A * B.submatrix σ id` for `A` lower triangular with nonzero diagonal.

## Tags

matrix, echelon form, rank, pivot
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : ℕ} {R : Type*}

/-- `l` is a pivot of `A`: a strictly increasing list of column indices whose `i`-th entry is
the leftmost nonzero column of row `i`, with every row from `l.length` on equal to zero. -/
structure IsPivot [Zero R] (A : Matrix (Fin m) (Fin n) R) (l : List (Fin n)) : Prop where
  sortedLT : l.SortedLT
  length_le : l.length ≤ m
  apply_eq_zero_of_lt (i : Fin m) (h : i < l.length) : ∀ j < l[i], A i j = 0
  apply_ne_zero (i : Fin m) (h : i < l.length) : A i l[i] ≠ 0
  row_eq_zero_of_length_le (i : Fin m) (h : l.length ≤ i) : A i = 0

theorem IsPivot.rowEchelon [Zero R] {A : Matrix (Fin m) (Fin n) R} {l : List (Fin n)}
    (h : A.IsPivot l) : A.RowEchelon := by
  intro i₁ i₂ hi₁₂ j₂ hj₂
  have hi₂ : i₂ < l.length :=
    not_le.mp fun hcon => hj₂ (congrFun (h.row_eq_zero_of_length_le i₂ hcon) j₂)
  have hi₁ : i₁ < l.length := lt_trans hi₁₂ hi₂
  have hle : l[i₂] ≤ j₂ :=
    not_lt.mp fun hcon => hj₂ (h.apply_eq_zero_of_lt i₂ hi₂ j₂ hcon)
  refine ⟨l[i₁], ?_, h.apply_ne_zero i₁ hi₁⟩
  exact (h.sortedLT.getElem_lt_getElem_of_lt hi₁₂).trans_le hle

protected theorem IsPivot.rank_eq [CommRing R] [IsDomain R] [StrongRankCondition R]
    {A : Matrix (Fin m) (Fin n) R} {l : List (Fin n)} (h : A.IsPivot l) :
    A.rank = l.length := by
  refine le_antisymm ?_ ?_
  · let S : Matrix (Fin m) (Fin l.length) R :=
      Matrix.of fun i a => if (a : ℕ) = (i : ℕ) then (1 : R) else 0
    have hS : S * A.submatrix (Fin.castLE h.length_le) id = A := by
      ext i j
      simp only [S, mul_apply, of_apply, submatrix_apply, id_eq]
      rcases lt_or_ge (i : ℕ) l.length with hi | hi
      · rw [Fintype.sum_eq_single (⟨(i : ℕ), hi⟩ : Fin l.length)
          fun b hb => by rw [if_neg fun he => hb (Fin.ext he), zero_mul],
          if_pos rfl, one_mul, Fin.castLE_mk, Fin.eta]
      · rw [congrFun (h.row_eq_zero_of_length_le i hi) j]
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [if_neg (a.2.trans_le hi).ne, zero_mul]
    calc A.rank = (S * A.submatrix (Fin.castLE h.length_le) id).rank := by rw [hS]
      _ ≤ (A.submatrix (Fin.castLE h.length_le) id).rank := rank_mul_le_right _ _
      _ ≤ Fintype.card (Fin l.length) := rank_le_card_height _
      _ = l.length := Fintype.card_fin _
  · have htri : (A.submatrix (Fin.castLE h.length_le) l.get).BlockTriangular id :=
      fun a b hab => h.apply_eq_zero_of_lt (Fin.castLE h.length_le a) a.2 _
        (h.sortedLT.strictMono_get hab)
    have hdet : (A.submatrix (Fin.castLE h.length_le) l.get).det ≠ 0 := by
      rw [det_of_upperTriangular htri]
      exact prod_ne_zero_iff.mpr fun a _ => h.apply_ne_zero (Fin.castLE h.length_le a) a.2
    calc l.length = (A.submatrix (Fin.castLE h.length_le) l.get).rank := by
          rw [rank_of_det_ne_zero hdet, Fintype.card_fin]
      _ ≤ A.rank := rank_submatrix_le A (Fin.castLE h.length_le) l.get

lemma rank_mul_eq_right_of_lowerTriangular [CommRing R] [IsDomain R]
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (σ : Equiv.Perm (Fin m))
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl (Fin n))

theorem IsPivot.rank_eq_of_lowerTriangular [CommRing R] [IsDomain R] [StrongRankCondition R]
    {A : Matrix (Fin m) (Fin m) R} {B : Matrix (Fin m) (Fin n) R} {σ : Equiv.Perm (Fin m)}
    {l : List (Fin n)} (hpiv : (A * B.submatrix σ id).IsPivot l)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) : B.rank = l.length := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

end Matrix

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
# Pivots of a matrix

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
  intro i₁ i₂ h₁₂ j₂ hz
  rcases lt_or_ge (i₂ : ℕ) l.length with hi₂ | hi₂
  · have hi₁ : i₁ < l.length := lt_trans h₁₂ hi₂
    have hle : j₂ ≤ l[i₁] := not_lt.mp fun hlt => h.apply_ne_zero i₁ hi₁ (hz _ hlt)
    exact h.apply_eq_zero_of_lt i₂ hi₂ j₂
      (hle.trans_lt (h.sortedLT.getElem_lt_getElem_of_lt h₁₂))
  · exact congrFun (h.row_eq_zero_of_length_le i₂ hi₂) j₂

theorem IsPivot.rank_eq [CommRing R] [IsDomain R]
    {A : Matrix (Fin m) (Fin n) R} {l : List (Fin n)} (h : A.IsPivot l) :
    A.rank = l.length := by
  refine le_antisymm ?_ ?_
  · refine (rank_le_card_of_row_eq_zero A
      (Finset.univ.map ⟨Fin.castLE h.length_le, Fin.castLE_injective _⟩)
      fun i hi => ?_).trans_eq (by simp)
    exact h.row_eq_zero_of_length_le i
      (not_lt.mp fun hlt => hi (Finset.mem_map.mpr ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩))
  · have htri : (A.submatrix (Fin.castLE h.length_le) l.get).BlockTriangular id :=
      fun a b hab => h.apply_eq_zero_of_lt (Fin.castLE h.length_le a) a.2 _
        (h.sortedLT.strictMono_get hab)
    have hdet : (A.submatrix (Fin.castLE h.length_le) l.get).det ≠ 0 := by
      rw [det_of_upperTriangular htri]
      exact prod_ne_zero_iff.mpr fun a _ => h.apply_ne_zero (Fin.castLE h.length_le a) a.2
    calc l.length = (A.submatrix (Fin.castLE h.length_le) l.get).rank := by
          rw [rank_of_det_ne_zero hdet, Fintype.card_fin]
      _ ≤ A.rank := rank_submatrix_le A (Fin.castLE h.length_le) l.get

theorem rank_mul_eq_right_of_lowerTriangular [CommRing R] [IsDomain R]
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (σ : Equiv.Perm (Fin m))
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl (Fin n))

theorem IsPivot.rank_eq_of_lowerTriangular [CommRing R] [IsDomain R]
    {A : Matrix (Fin m) (Fin m) R} {B : Matrix (Fin m) (Fin n) R} {σ : Equiv.Perm (Fin m)}
    {l : List (Fin n)} (hpiv : (A * B.submatrix σ id).IsPivot l)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) : B.rank = l.length := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

/-! ## Decidability

`IsPivot` and `BlockTriangular` are decidable over a `DecidableEq` ring, so a certified
`(T, σ, l)` computed off-kernel can be checked by `decide +kernel` directly on the matrix. -/

instance decidableIsPivot [Zero R] [DecidableEq R] (A : Matrix (Fin m) (Fin n) R)
    (l : List (Fin n)) : Decidable (A.IsPivot l) := by
  haveI : ∀ i : Fin m, Decidable (∀ _ : (i : ℕ) < l.length, ∀ j < l[i], A i j = 0) :=
    fun _ => inferInstance
  haveI : ∀ i : Fin m, Decidable (∀ _ : l.length ≤ (i : ℕ), A i = 0) := fun _ => inferInstance
  refine decidable_of_iff'
    (l.SortedLT ∧ l.length ≤ m ∧
      (∀ i : Fin m, ∀ _ : (i : ℕ) < l.length, ∀ j < l[i], A i j = 0) ∧
      (∀ i : Fin m, ∀ _ : (i : ℕ) < l.length, A i l[i] ≠ 0) ∧
      (∀ i : Fin m, ∀ _ : l.length ≤ (i : ℕ), A i = 0)) ?_
  constructor
  · rintro ⟨hs, hle, h₃, h₄, h₅⟩
    exact ⟨hs, hle, h₃, h₄, h₅⟩
  · rintro ⟨hs, hle, h₃, h₄, h₅⟩
    exact ⟨hs, hle, h₃, h₄, h₅⟩

/- Alternative: a hand-rolled `Bool` decision procedure
reflected back to `IsPivot`. Kernel cost is within ~5-8% of the instance above across full-rank
and rank-deficient cases up to 24×40; its sole advantage is the single seam (`isPivotB`'s body)
where a packed product check could later replace the naive per-entry scan.

def isPivotB [Zero R] [DecidableEq R] (A : Matrix (Fin m) (Fin n) R) (l : List (Fin n)) : Bool :=
  decide l.SortedLT && decide (l.length ≤ m) &&
    (List.finRange m).all fun i =>
      if hi : (i : ℕ) < l.length then
        (List.finRange n).all (fun j => decide (j < l[(i : ℕ)] → A i j = 0)) &&
          decide (A i l[(i : ℕ)] ≠ 0)
      else
        (List.finRange n).all fun j => decide (A i j = 0)

theorem isPivotB_iff [Zero R] [DecidableEq R] (A : Matrix (Fin m) (Fin n) R) (l : List (Fin n)) :
    isPivotB A l = true ↔ A.IsPivot l := by
  rw [isPivotB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_finRange, forall_const]
  constructor
  · rintro ⟨⟨hs, hle⟩, hrow⟩
    refine ⟨hs, hle, ?_, ?_, ?_⟩
    · intro i h j hj
      have hi := hrow i
      rw [dif_pos h, Bool.and_eq_true, List.all_eq_true] at hi
      have := hi.1 j (List.mem_finRange j)
      rw [decide_eq_true_eq] at this
      exact this hj
    · intro i h
      have hi := hrow i
      rw [dif_pos h, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact hi.2
    · intro i h
      funext j
      have hi := hrow i
      rw [dif_neg (by omega), List.all_eq_true] at hi
      have := hi j (List.mem_finRange j)
      rw [decide_eq_true_eq] at this
      exact this
  · intro hp
    refine ⟨⟨hp.sortedLT, hp.length_le⟩, ?_⟩
    intro i
    by_cases h : (i : ℕ) < l.length
    · rw [dif_pos h, Bool.and_eq_true, List.all_eq_true]
      refine ⟨fun j _ => ?_, ?_⟩
      · rw [decide_eq_true_eq]
        exact fun hj => hp.apply_eq_zero_of_lt i h j hj
      · rw [decide_eq_true_eq]
        exact hp.apply_ne_zero i h
    · rw [dif_neg h, List.all_eq_true]
      intro j _
      rw [decide_eq_true_eq]
      exact congrFun (hp.row_eq_zero_of_length_le i (by omega)) j

instance decidableIsPivot [Zero R] [DecidableEq R] (A : Matrix (Fin m) (Fin n) R)
    (l : List (Fin n)) : Decidable (A.IsPivot l) :=
  decidable_of_iff _ (isPivotB_iff A l)
-/

end Matrix

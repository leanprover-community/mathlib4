/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Finset.Sort
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pivots of a matrix, `Finset` formulation (draft)

A standalone parallel of `Pivot.lean` carrying the pivot columns as a `Finset (Fin n)`
instead of a strictly increasing `List (Fin n)`; the `i`-th pivot is recovered through
`Finset.orderEmbOfFin`. Drafted to compare the two carriers; not imported by anything.

-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : ℕ} {R : Type*}

/-- `s` is a pivot set of `A`: the `i`-th smallest element of `s` is the leftmost nonzero
column of row `i`, with every row from `s.card` on equal to zero. -/
structure IsPivotFinset [Zero R] (A : Matrix (Fin m) (Fin n) R) (s : Finset (Fin n)) :
    Prop where
  card_le : s.card ≤ m
  apply_eq_zero_of_lt (i : Fin m) (h : (i : ℕ) < s.card) :
    ∀ j < s.orderEmbOfFin rfl ⟨i, h⟩, A i j = 0
  apply_ne_zero (i : Fin m) (h : (i : ℕ) < s.card) : A i (s.orderEmbOfFin rfl ⟨i, h⟩) ≠ 0
  row_eq_zero_of_card_le (i : Fin m) (h : s.card ≤ (i : ℕ)) : A i = 0

theorem IsPivotFinset.rowEchelon [Zero R] {A : Matrix (Fin m) (Fin n) R} {s : Finset (Fin n)}
    (h : A.IsPivotFinset s) : A.RowEchelon := by
  intro i₁ i₂ h₁₂ j₂ hz
  rcases lt_or_ge (i₂ : ℕ) s.card with hi₂ | hi₂
  · have hi₁ : (i₁ : ℕ) < s.card := lt_trans h₁₂ hi₂
    have hle : j₂ ≤ s.orderEmbOfFin rfl ⟨i₁, hi₁⟩ :=
      not_lt.mp fun hlt => h.apply_ne_zero i₁ hi₁ (hz _ hlt)
    exact h.apply_eq_zero_of_lt i₂ hi₂ j₂
      (hle.trans_lt ((s.orderEmbOfFin rfl).strictMono h₁₂))
  · exact congrFun (h.row_eq_zero_of_card_le i₂ hi₂) j₂

theorem IsPivotFinset.rank_eq [CommRing R] [IsDomain R]
    {A : Matrix (Fin m) (Fin n) R} {s : Finset (Fin n)} (h : A.IsPivotFinset s) :
    A.rank = s.card := by
  refine le_antisymm ?_ ?_
  · refine (rank_le_card_of_row_eq_zero A
      (Finset.univ.map ⟨Fin.castLE h.card_le, Fin.castLE_injective _⟩)
      fun i hi => ?_).trans_eq (by simp)
    exact h.row_eq_zero_of_card_le i
      (not_lt.mp fun hlt => hi (Finset.mem_map.mpr ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩))
  · have htri : (A.submatrix (Fin.castLE h.card_le) (s.orderEmbOfFin rfl)).BlockTriangular id :=
      fun a b hab => h.apply_eq_zero_of_lt (Fin.castLE h.card_le a) a.2 _
        ((s.orderEmbOfFin rfl).strictMono hab)
    have hdet : (A.submatrix (Fin.castLE h.card_le) (s.orderEmbOfFin rfl)).det ≠ 0 := by
      rw [det_of_upperTriangular htri]
      exact prod_ne_zero_iff.mpr fun a _ => h.apply_ne_zero (Fin.castLE h.card_le a) a.2
    calc s.card = (A.submatrix (Fin.castLE h.card_le) (s.orderEmbOfFin rfl)).rank := by
          rw [rank_of_det_ne_zero hdet, Fintype.card_fin]
      _ ≤ A.rank := rank_submatrix_le A (Fin.castLE h.card_le) (s.orderEmbOfFin rfl)

lemma rank_mul_eq_right_of_lowerTriangular [CommRing R] [IsDomain R]
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin n) R) (σ : Equiv.Perm (Fin m))
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl (Fin n))

theorem IsPivotFinset.rank_eq_of_lowerTriangular [CommRing R] [IsDomain R]
    {A : Matrix (Fin m) (Fin m) R} {B : Matrix (Fin m) (Fin n) R} {σ : Equiv.Perm (Fin m)}
    {s : Finset (Fin n)} (hpiv : (A * B.submatrix σ id).IsPivotFinset s)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) : B.rank = s.card := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

/-! ## Decidability

`IsPivotFinset` and `BlockTriangular` are decidable over a `DecidableEq` ring, so a certified
`(T, σ, s)` computed off-kernel can be checked by `decide +kernel` directly on the matrix. -/

instance decidableIsPivotFinset [Zero R] [DecidableEq R] (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) : Decidable (A.IsPivotFinset s) := by
  haveI : ∀ i : Fin m,
      Decidable (∀ h : (i : ℕ) < s.card, ∀ j < s.orderEmbOfFin rfl ⟨i, h⟩, A i j = 0) :=
    fun _ => inferInstance
  haveI : ∀ i : Fin m, Decidable (∀ _ : s.card ≤ (i : ℕ), A i = 0) := fun _ => inferInstance
  refine decidable_of_iff'
    (s.card ≤ m ∧
      (∀ i : Fin m, ∀ h : (i : ℕ) < s.card, ∀ j < s.orderEmbOfFin rfl ⟨i, h⟩, A i j = 0) ∧
      (∀ i : Fin m, ∀ h : (i : ℕ) < s.card, A i (s.orderEmbOfFin rfl ⟨i, h⟩) ≠ 0) ∧
      (∀ i : Fin m, ∀ _ : s.card ≤ (i : ℕ), A i = 0)) ?_
  constructor
  · rintro ⟨hc, h₂, h₃, h₄⟩
    exact ⟨hc, h₂, h₃, h₄⟩
  · rintro ⟨hc, h₂, h₃, h₄⟩
    exact ⟨hc, h₂, h₃, h₄⟩

end Matrix

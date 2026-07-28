/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Pivot maps of a matrix

The pivot map of a matrix in row echelon form sends each row to its leading (leftmost
nonzero) column, or to `⊤` for a zero row. The number of rows with a pivot is the rank,
which lets the rank be read off a `T * (P * M)` decomposition (`T` lower triangular with
nonzero diagonal, `P` a row permutation) without materialising the product. `IsRowEchelon`
is a primitive field of the structure and the staircase conditions are derived; see
`Pivot_structural.lean` for the opposite packaging.

## Main definitions

- `Matrix.IsPivot`: `l : m → WithTop n` is the pivot map of `A`.

## Main results

- `Matrix.IsPivot.rank_eq`: a matrix with pivot map `l` has rank the number of rows
  with a pivot.
- `Matrix.IsPivot.unique`: the pivot map of a matrix is unique.
- `Matrix.IsPivot.rank_eq_of_lowerTriangular`: the rank of `B`, read off a pivot map
  of `A * B.submatrix σ id` for `A` lower triangular with nonzero diagonal.
- `Matrix.decidableIsPivot`: `IsPivot` is decidable over a `DecidableEq` ring and
  finite linearly ordered indices.

## Tags

matrix, echelon form, rank, pivot
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : Type*} {R : Type*}

section Zero

variable [Zero R] {A : Matrix m n R} {l : m → WithTop n}

/-- `l` is the pivot map of `A`: the matrix is in row echelon form and `l` sends each row
to its leading position. -/
structure IsPivot [LT m] [LT n] (A : Matrix m n R) (l : m → WithTop n) : Prop where
  isRowEchelon : A.IsRowEchelon
  isLeadingEntry : ∀ i : m, A.IsLeadingEntry i (l i)

theorem IsPivot.eq_top_iff [LT m] [LT n] {i : m} (h : A.IsPivot l) :
    l i = ⊤ ↔ A i = 0 := by
  cases hc : l i with
  | top => simpa using isLeadingEntry_top_iff.mp (hc ▸ h.isLeadingEntry i)
  | coe c => simpa using fun h0 => (h.isLeadingEntry i).2 c hc (congrFun h0 c)

theorem IsPivot.lt_of_lt_of_ne_top [LT m] [LinearOrder n] {i₁ i₂ : m}
    (h : A.IsPivot l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  by_contra! hle
  obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp (hle.trans_lt h₁.lt_top).ne
  refine (h.isLeadingEntry i₂).2 c₂ hc₂.symm (h.isRowEchelon hlt fun j₁ hj₁ => ?_)
  exact (h.isLeadingEntry i₁).1 j₁ ((WithTop.coe_lt_coe.mpr hj₁).trans_le (hc₂.le.trans hle))

theorem IsPivot.monotone [PartialOrder m] [LinearOrder n] (h : A.IsPivot l) :
    Monotone l := by
  refine monotone_iff_forall_lt.mpr ?_
  intro i₁ i₂ hlt
  by_cases h₁ : l i₁ = ⊤
  · simp [h.eq_top_iff.mpr (h.isRowEchelon.row_eq_zero_of_lt hlt (h.eq_top_iff.mp h₁))]
  · exact (h.lt_of_lt_of_ne_top hlt h₁).le

theorem IsPivot.strictMonoOn [Preorder m] [LinearOrder n] (h : A.IsPivot l) :
    StrictMonoOn l {i | l i ≠ ⊤} :=
  fun _ h₁ _ _ hlt => h.lt_of_lt_of_ne_top hlt h₁

/-- The pivot map of a matrix is unique. -/
theorem IsPivot.unique [LT m] [LinearOrder n] {l' : m → WithTop n}
    (h : A.IsPivot l) (h' : A.IsPivot l') : l = l' :=
  funext fun i => (h.isLeadingEntry i).unique (h'.isLeadingEntry i)

/-- The staircase characterisation of a pivot map. -/
theorem isPivot_iff [PartialOrder m] [LinearOrder n] :
    A.IsPivot l ↔
      Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧ ∀ i : m, A.IsLeadingEntry i (l i) := by
  refine ⟨fun h => ⟨h.monotone, h.strictMonoOn, h.isLeadingEntry⟩, ?_⟩
  rintro ⟨hmono, hstrict, hlead⟩
  refine ⟨?_, hlead⟩
  intro i₁ i₂ hlt j₂ hz
  refine (hlead i₂).1 j₂ ?_
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · exact h₂ ▸ WithTop.coe_lt_top j₂
  · have h₁ : l i₁ ≠ ⊤ := fun ht => h₂ (top_le_iff.mp (ht ▸ hmono hlt.le))
    obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
    have hj : (j₂ : WithTop n) ≤ c₁ :=
      WithTop.coe_le_coe.mpr <| le_of_not_gt fun hgt => (hlead i₁).2 c₁ hc₁.symm (hz c₁ hgt)
    exact lt_of_le_of_lt (hc₁ ▸ hj) (hstrict h₁ h₂ hlt)

end Zero

theorem rank_mul_eq_right_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
    [CommRing R] [IsDomain R] (A : Matrix m m R) (B : Matrix m n R) (σ : Equiv.Perm m)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl n)

section Rank

variable [Fintype m] [Fintype n] {A : Matrix m n R} {l : m → WithTop n}

theorem IsPivot.rank_le_card [LT m] [LT n] [DecidableEq n] [CommSemiring R]
    [StrongRankCondition R] (h : A.IsPivot l) : A.rank ≤ #{i | l i ≠ ⊤} :=
  A.rank_le_card_of_row_eq_zero _ fun i hi => h.eq_top_iff.mp (by simpa using hi)

variable [LinearOrder m] [LinearOrder n] [CommRing R] [IsDomain R]

theorem IsPivot.card_le_rank (h : A.IsPivot l) : #{i | l i ≠ ⊤} ≤ A.rank := by
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i, (∀ j < g i, A i.1 j = 0) ∧ A i.1 (g i) ≠ 0 := by
    intro i
    have hl := h.isLeadingEntry i.1
    rw [← WithTop.coe_untop (l i.1) i.2, isLeadingEntry_coe_iff] at hl
    exact hl
  have htri : (A.submatrix Subtype.val g).BlockTriangular id := by
    intro i j hij
    exact (hlead i).1 _ ((WithTop.untop_lt_untop_iff _ _).mpr (h.strictMonoOn j.2 i.2 hij))
  have hdet : (A.submatrix Subtype.val g).det ≠ 0 := by
    rw [det_of_upperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hlead i).2
  calc #{i | l i ≠ ⊤}
      = (A.submatrix Subtype.val g).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_subtype]
    _ ≤ A.rank := rank_submatrix_le A Subtype.val g

theorem IsPivot.rank_eq (h : A.IsPivot l) : A.rank = #{i | l i ≠ ⊤} :=
  le_antisymm h.rank_le_card h.card_le_rank

theorem IsPivot.rank_eq_of_lowerTriangular {A : Matrix m m R} {B : Matrix m n R}
    {σ : Equiv.Perm m} (hpiv : (A * B.submatrix σ id).IsPivot l)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    B.rank = #{i | l i ≠ ⊤} :=
  (rank_mul_eq_right_of_lowerTriangular A B σ hA hd).symm.trans hpiv.rank_eq

end Rank

/-! ## Decidability -/

section Decidability

variable [Zero R] [DecidableEq R]

instance decidableIsLeadingEntry [Fintype n] [LT n] [DecidableLT n] [DecidableEq n]
    (A : Matrix m n R) (i : m) (c : WithTop n) : Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff
    ((∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0) Iff.rfl

instance decidableIsPivot [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (l : m → WithTop n) : Decidable (A.IsPivot l) :=
  decidable_of_iff' _ isPivot_iff

end Decidability

end Matrix

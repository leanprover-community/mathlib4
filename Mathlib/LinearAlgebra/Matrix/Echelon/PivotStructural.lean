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
# Pivots of a matrix

`Matrix.IsPivot A l` defines a map-based representation `l` for the pivot, stating that
`l i` is the pivot column of each row `i` of `A`, with `⊤` for a zero row.

## Main definitions

- `Matrix.IsPivot`: `l i : WithTop n` is the pivot column of each row `i` of `A`.

## Main results

- `Matrix.IsPivot.rank_eq`: the rank of a matrix is its number of pivots.
- `Matrix.IsPivot.unique`: the pivots of a matrix are unique.
- `Matrix.IsPivot.rank_eq_of_lowerTriangular`: the rank of `B` from the pivots of
  `A * B.submatrix σ id`, for `A` lower triangular with nonzero diagonal.
- `Matrix.decidableIsPivot`: `IsPivot` is decidable over a `DecidableEq` ring and
  finite linearly ordered indices.

## Tags

matrix, echelon form, pivot
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : Type*} {R : Type*}

section Zero

variable [Zero R] [Preorder m] {A : Matrix m n R} {l : m → WithTop n}

/-- `l i` is the leading position of each row `i` of `A`; `l` is monotone and strictly
increasing on the nonzero rows. -/
structure IsPivot [Preorder n] (A : Matrix m n R) (l : m → WithTop n) :
    Prop where
  monotone : Monotone l
  strictMonoOn : StrictMonoOn l {i | l i ≠ ⊤}
  isLeadingEntry : ∀ i : m, A.IsLeadingEntry i (l i)

theorem IsPivot.lt_of_lt_of_ne_top [Preorder n] {i₁ i₂ : m}
    (hA : A.IsPivot l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · exact h₂ ▸ WithTop.lt_top_iff_ne_top.mpr h₁
  · exact hA.strictMonoOn h₁ h₂ hlt

variable [LinearOrder n]

theorem IsPivot.isRowEchelon (hA : A.IsPivot l) : A.IsRowEchelon := by
  intro i₁ i₂ hlt j₂ hz
  refine (hA.isLeadingEntry i₂).1 j₂ ?_
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · rw [h₂]
    exact WithTop.coe_lt_top j₂
  · have h₁ : l i₁ ≠ ⊤ := fun ht => h₂ (top_le_iff.mp (ht ▸ hA.monotone hlt.le))
    obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
    have hj : (j₂ : WithTop n) ≤ c₁ := WithTop.coe_le_coe.mpr <| le_of_not_gt fun hgt =>
      (hA.isLeadingEntry i₁).2 c₁ hc₁.symm (hz c₁ hgt)
    exact lt_of_le_of_lt (hc₁ ▸ hj) (hA.lt_of_lt_of_ne_top hlt h₁)

/-- The pivots of a matrix are unique. -/
theorem IsPivot.unique {l' : m → WithTop n}
    (hl : A.IsPivot l) (hl' : A.IsPivot l') : l = l' :=
  funext fun i => (hl.isLeadingEntry i).unique (hl'.isLeadingEntry i)

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

variable [Fintype m] [Fintype n] [Preorder n] [DecidableEq n] {A : Matrix m n R}
  {l : m → WithTop n}

theorem IsPivot.rank_le_card [Preorder m] [CommSemiring R] [StrongRankCondition R]
    (hA : A.IsPivot l) : A.rank ≤ #{i | l i ≠ ⊤} := by
  refine A.rank_le_card_of_row_eq_zero _ fun i hi => ?_
  have htop : l i = ⊤ := by simpa using hi
  exact isLeadingEntry_top_iff.mp (htop ▸ hA.isLeadingEntry i)

variable [LinearOrder m] [CommRing R] [IsDomain R]

theorem IsPivot.card_le_rank (hA : A.IsPivot l) : #{i | l i ≠ ⊤} ≤ A.rank := by
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i, (∀ j < g i, A i.1 j = 0) ∧ A i.1 (g i) ≠ 0 := by
    intro i
    have hl := hA.isLeadingEntry i.1
    rw [← WithTop.coe_untop (l i.1) i.2, isLeadingEntry_coe_iff] at hl
    exact hl
  have htri : (A.submatrix Subtype.val g).BlockTriangular id := by
    intro i j hij
    exact (hlead i).1 _ ((WithTop.untop_lt_untop_iff _ _).mpr (hA.strictMonoOn j.2 i.2 hij))
  have hdet : (A.submatrix Subtype.val g).det ≠ 0 := by
    rw [det_of_upperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hlead i).2
  calc #{i | l i ≠ ⊤}
      = (A.submatrix Subtype.val g).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_subtype]
    _ ≤ A.rank := rank_submatrix_le A Subtype.val g

theorem IsPivot.rank_eq (hA : A.IsPivot l) : A.rank = #{i | l i ≠ ⊤} :=
  le_antisymm hA.rank_le_card hA.card_le_rank

theorem IsPivot.rank_eq_of_lowerTriangular {A : Matrix m m R} {B : Matrix m n R}
    {σ : Equiv.Perm m} (hpiv : (A * B.submatrix σ id).IsPivot l)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    B.rank = #{i | l i ≠ ⊤} := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

end Rank

/-! ## Decidability
  The instances decide the automatically synthesised staircase proposition; a hand-rolled
  boolean checker is an open consideration. -/

section Decidability

variable [Zero R] [DecidableEq R]

instance decidableIsLeadingEntry [Fintype n] [LT n] [DecidableLT n] [DecidableEq n]
    (A : Matrix m n R) (i : m) (c : WithTop n) : Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff
    ((∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0) Iff.rfl

instance decidableIsPivot [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (l : m → WithTop n) : Decidable (A.IsPivot l) :=
  decidable_of_iff'
    (Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧ ∀ i : m, A.IsLeadingEntry i (l i))
    ⟨fun h => ⟨h.monotone, h.strictMonoOn, h.isLeadingEntry⟩,
      fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end Decidability

end Matrix

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
- `Matrix.IsPivot.unique`: the pivot of a matrix is unique if the column indices have a linear
  order.
- `Matrix.decidableIsPivot`: A decidable instance for `IsPivot` over a `DecidableEq` ring and
  linearly ordered indices.

## Tags

matrix, echelon form, pivot
-/

@[expose] public section

namespace Matrix

open Finset

variable {m n : Type*} {R : Type*}

section Zero

variable [Zero R] {A : Matrix m n R} {l : m → WithTop n}

/-- `A` is in row echelon form and `l i` is the leading position of each row `i`. -/
structure IsPivot [LT m] [LT n] (A : Matrix m n R) (l : m → WithTop n) : Prop where
  isRowEchelon : A.IsRowEchelon
  isLeadingEntry : ∀ i : m, A.IsLeadingEntry i (l i)

theorem IsPivot.eq_top_iff [LT m] [LT n] {i : m} (hA : A.IsPivot l) :
    l i = ⊤ ↔ A i = 0 := by
  cases hc : l i with
  | top => simpa using isLeadingEntry_top_iff.mp (hc ▸ hA.isLeadingEntry i)
  | coe c => simpa using fun h0 => (hA.isLeadingEntry i).2 c hc (congrFun h0 c)

variable [LinearOrder n]

theorem IsPivot.lt_of_lt_of_ne_top [LT m] {i₁ i₂ : m}
    (hA : A.IsPivot l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  by_contra! hle
  obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp (hle.trans_lt h₁.lt_top).ne
  refine (hA.isLeadingEntry i₂).2 c₂ hc₂.symm (hA.isRowEchelon hlt fun j₁ hj₁ => ?_)
  exact (hA.isLeadingEntry i₁).1 j₁ ((WithTop.coe_lt_coe.mpr hj₁).trans_le (hc₂.le.trans hle))

/-- The pivots of a matrix are unique. -/
theorem IsPivot.unique [LT m] {l' : m → WithTop n}
    (hl : A.IsPivot l) (hl' : A.IsPivot l') : l = l' :=
  funext fun i => (hl.isLeadingEntry i).unique (hl'.isLeadingEntry i)

theorem IsPivot.strictMonoOn [Preorder m] (hA : A.IsPivot l) :
    StrictMonoOn l {i | l i ≠ ⊤} :=
  fun _ h₁ _ _ hlt => hA.lt_of_lt_of_ne_top hlt h₁

variable [PartialOrder m]

theorem IsPivot.monotone (hA : A.IsPivot l) :
    Monotone l := by
  refine monotone_iff_forall_lt.mpr ?_
  intro i₁ i₂ hlt
  by_cases h₁ : l i₁ = ⊤
  · simp [hA.eq_top_iff.mpr (hA.isRowEchelon.row_eq_zero_of_lt hlt (hA.eq_top_iff.mp h₁))]
  · exact (hA.lt_of_lt_of_ne_top hlt h₁).le

/-- The map-structural characterisation of pivots. This is useful for proving that
a matrix is in row echelon form. -/
theorem isPivot_iff :
    A.IsPivot l ↔
      Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧ ∀ i : m, A.IsLeadingEntry i (l i) := by
  refine ⟨fun hA => ⟨hA.monotone, hA.strictMonoOn, hA.isLeadingEntry⟩, ?_⟩
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

section Rank

variable [Fintype m] [Fintype n] {A : Matrix m n R} {l : m → WithTop n}

theorem IsPivot.rank_le_card [LT m] [LT n] [DecidableEq n] [CommSemiring R]
    [StrongRankCondition R] (hA : A.IsPivot l) : A.rank ≤ #{i | l i ≠ ⊤} :=
  A.rank_le_card_of_row_eq_zero _ fun i hi => hA.eq_top_iff.mp (by simpa using hi)

variable [LinearOrder m] [LinearOrder n] [CommRing R] [IsDomain R]

theorem IsPivot.card_le_rank (hA : A.IsPivot l) : #{i | l i ≠ ⊤} ≤ A.rank := by
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i, (∀ j < g i, A i.1 j = 0) ∧ A i.1 (g i) ≠ 0 := by
    intro i
    have hl := hA.isLeadingEntry i.1
    rw [← WithTop.coe_untop (l i.1) i.2, isLeadingEntry_coe_iff] at hl
    exact hl
  have htri : (A.submatrix Subtype.val g).IsUpperTriangular := by
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

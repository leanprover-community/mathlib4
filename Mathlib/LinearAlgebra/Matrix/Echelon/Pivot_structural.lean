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
# Pivot maps of a matrix, structural formulation

The pivot map of a matrix in row echelon form sends each row to its leading (leftmost
nonzero) column, or to `⊤` for a zero row. In this packaging the staircase conditions
(`Monotone`, `StrictMonoOn` off the `⊤`-fiber) are the structure fields and `RowEchelon`
is derived; see `Pivot.lean` for the packaging with `RowEchelon` primitive.

## Main definitions

- `Matrix.IsPivotMap`: `l : m → WithTop n` is the pivot map of `A`.

## Main results

- `Matrix.IsPivotMap.rank_eq`: a matrix with pivot map `l` has rank the number of rows
  with a pivot.
- `Matrix.IsPivotMap.unique`: the pivot map of a matrix is unique.
- `Matrix.IsPivotMap.rank_eq_of_lowerTriangular`: the rank of `B`, read off a pivot map
  of `A * B.submatrix σ id` for `A` lower triangular with nonzero diagonal.
- `Matrix.decidableIsPivotMap`: `IsPivotMap` is decidable over a `DecidableEq` ring and
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

/-- `l` is the pivot map of `A`: it sends each row to its leading position, is monotone,
and strictly increases on the nonzero rows. -/
structure IsPivotMap [Preorder m] [Preorder n] (A : Matrix m n R) (l : m → WithTop n) :
    Prop where
  monotone : Monotone l
  strictMonoOn : StrictMonoOn l {i | l i ≠ ⊤}
  isLeadingEntry : ∀ i : m, A.IsLeadingEntry i (l i)

theorem IsPivotMap.lt_of_lt_of_ne_top [Preorder m] [Preorder n] {i₁ i₂ : m}
    (h : A.IsPivotMap l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · exact h₂ ▸ WithTop.lt_top_iff_ne_top.mpr h₁
  · exact h.strictMonoOn h₁ h₂ hlt

theorem IsPivotMap.rowEchelon [Preorder m] [LinearOrder n] (h : A.IsPivotMap l) :
    A.RowEchelon := by
  intro i₁ i₂ hlt j₂ hz
  refine (h.isLeadingEntry i₂).1 j₂ ?_
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · rw [h₂]
    exact WithTop.coe_lt_top j₂
  · have h₁ : l i₁ ≠ ⊤ := fun ht => h₂ (top_le_iff.mp (ht ▸ h.monotone hlt.le))
    refine lt_of_le_of_lt (not_lt.mp fun hc => ?_) (h.lt_of_lt_of_ne_top hlt h₁)
    obtain ⟨c₁, hc₁, hcj⟩ := WithTop.lt_iff_exists_coe.mp hc
    exact (h.isLeadingEntry i₁).2 c₁ hc₁ (hz c₁ (WithTop.coe_lt_coe.mp hcj))

/-- The pivot map of a matrix is unique. -/
theorem IsPivotMap.unique [Preorder m] [LinearOrder n] {l' : m → WithTop n}
    (h : A.IsPivotMap l) (h' : A.IsPivotMap l') : l = l' :=
  funext fun i => (h.isLeadingEntry i).unique (h'.isLeadingEntry i)

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

theorem IsPivotMap.rank_le_card [Preorder m] [CommSemiring R] [StrongRankCondition R]
    (h : A.IsPivotMap l) : A.rank ≤ #{i | l i ≠ ⊤} :=
  rank_le_card_of_row_eq_zero A _ fun i hi =>
    isLeadingEntry_top_iff.mp
      (of_not_not (fun hne => hi ((mem_filter_univ i).mpr hne)) ▸ h.isLeadingEntry i)

variable [LinearOrder m] [CommRing R] [IsDomain R]

theorem IsPivotMap.card_le_rank (h : A.IsPivotMap l) : #{i | l i ≠ ⊤} ≤ A.rank := by
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i, (∀ j < g i, A i.1 j = 0) ∧ A i.1 (g i) ≠ 0 := by
    intro i
    have hl := h.isLeadingEntry i.1
    rw [← WithTop.coe_untop (l i.1) i.2, isLeadingEntry_coe_iff] at hl
    exact hl
  have htri : (A.submatrix Subtype.val g).BlockTriangular id := fun i j hij =>
    (hlead i).1 _ ((WithTop.untop_lt_untop_iff _ _).mpr (h.strictMonoOn j.2 i.2 hij))
  have hdet : (A.submatrix Subtype.val g).det ≠ 0 := by
    rw [det_of_upperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hlead i).2
  calc #{i | l i ≠ ⊤}
      = (A.submatrix Subtype.val g).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_subtype]
    _ ≤ A.rank := rank_submatrix_le A Subtype.val g

theorem IsPivotMap.rank_eq (h : A.IsPivotMap l) : A.rank = #{i | l i ≠ ⊤} :=
  le_antisymm h.rank_le_card h.card_le_rank

theorem IsPivotMap.rank_eq_of_lowerTriangular {A : Matrix m m R} {B : Matrix m n R}
    {σ : Equiv.Perm m} (hpiv : (A * B.submatrix σ id).IsPivotMap l)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    B.rank = #{i | l i ≠ ⊤} := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

end Rank

/-! ## Decidability
  This uses the automatically synthesised version as well -- same as the list-based
  pivot def. The same consideration for a boolean version is open.
 -/

section Decidability

variable [Zero R] [DecidableEq R]

instance decidableIsLeadingEntry [Fintype n] [LT n] [DecidableLT n] [DecidableEq n]
    (A : Matrix m n R) (i : m) (c : WithTop n) : Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff
    ((∀ j : n, (j : WithTop n) < c → A i j = 0) ∧ ∀ c₀ : n, c = c₀ → A i c₀ ≠ 0) Iff.rfl

instance decidableIsPivotMap [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (l : m → WithTop n) : Decidable (A.IsPivotMap l) :=
  decidable_of_iff'
    (Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧ ∀ i : m, A.IsLeadingEntry i (l i))
    ⟨fun h => ⟨h.monotone, h.strictMonoOn, h.isLeadingEntry⟩,
      fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

end Decidability

end Matrix

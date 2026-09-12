/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Echelon.Basic
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Order.WithBot

/-!
# Pivots of a matrix

`Matrix.IsPivotedBy A l` defines a map-based representation `l` for the pivot, stating that
`l i` is the pivot column of each row `i` of `A`, with `⊤` for a zero row.

## Main definitions

- `Matrix.IsPivotedBy`: `l i : WithTop n` is the pivot column of each row `i` of `A`.

## Main results

- `Matrix.IsPivotedBy.rank_eq`: the rank of a matrix is its number of pivots.
- `Matrix.IsPivotedBy.unique`: the pivot of a matrix is unique if the column indices have a
  linear order.
- `Matrix.isPivotedBy_iff`: the map-structural characterisation of pivots.

## Tags

matrix, echelon form, pivot
-/

@[expose] public section

namespace Matrix

open Finset

variable {m n : Type*} {R : Type*}

section Zero

variable [Zero R] {A : Matrix m n R} {l : m → WithTop n}

/-- `A` is in row echelon form and `l i` is the leading position of each row `i`,
with `⊤` for a zero row. -/
structure IsPivotedBy [LT m] [LT n] (A : Matrix m n R) (l : m → WithTop n) : Prop where
  isRowEchelon : A.IsRowEchelon
  isPivotEntry (i : m) :
    (∀ j : n, (j : WithTop n) < l i → A i j = 0) ∧ ∀ c : n, l i = c → A i c ≠ 0

namespace IsPivotedBy

theorem isLeadingEntry [LT m] [LT n] {i : m} {c : n} (hA : A.IsPivotedBy l) (hc : l i = c) :
    A.IsLeadingEntry i c := by
  refine ⟨fun j hj => (hA.isPivotEntry i).1 j ?_, (hA.isPivotEntry i).2 c hc⟩
  rw [hc]
  exact_mod_cast hj

theorem eq_top_iff [LT m] [LT n] {i : m} (hA : A.IsPivotedBy l) :
    l i = ⊤ ↔ A i = 0 := by
  cases hc : l i with
  | top =>
    have h := (hA.isPivotEntry i).1
    rw [hc] at h
    simpa [funext_iff] using fun j => h j (WithTop.coe_lt_top j)
  | coe c => simpa using fun h0 => (hA.isPivotEntry i).2 c hc (congrFun h0 c)

variable [LinearOrder n]

theorem lt_of_lt_of_ne_top [LT m] {i₁ i₂ : m}
    (hA : A.IsPivotedBy l) (hlt : i₁ < i₂) (h₁ : l i₁ ≠ ⊤) : l i₁ < l i₂ := by
  by_contra! hle
  obtain ⟨c₂, hc₂⟩ := WithTop.ne_top_iff_exists.mp (hle.trans_lt h₁.lt_top).ne
  refine (hA.isPivotEntry i₂).2 c₂ hc₂.symm (hA.isRowEchelon hlt fun j₁ hj₁ => ?_)
  exact (hA.isPivotEntry i₁).1 j₁ ((WithTop.coe_lt_coe.mpr hj₁).trans_le (hc₂.le.trans hle))

/-- The pivots of a matrix are unique. -/
theorem unique [LT m] {l' : m → WithTop n}
    (hl : A.IsPivotedBy l) (hl' : A.IsPivotedBy l') : l = l' := by
  funext i
  cases hc' : l' i with
  | top =>
    rw [hl.eq_top_iff, ← hl'.eq_top_iff]
    exact hc'
  | coe c' =>
    cases hc : l i with
    | top =>
      rw [hl.eq_top_iff] at hc
      exact absurd (congrFun hc c') (hl'.isLeadingEntry hc').2
    | coe c => exact_mod_cast (hl.isLeadingEntry hc).unique (hl'.isLeadingEntry hc')

theorem strictMonoOn [Preorder m] (hA : A.IsPivotedBy l) :
    StrictMonoOn l {i | l i ≠ ⊤} :=
  fun _ h₁ _ _ hlt => hA.lt_of_lt_of_ne_top hlt h₁

variable [PartialOrder m]

theorem monotone (hA : A.IsPivotedBy l) :
    Monotone l := by
  refine monotone_iff_forall_lt.mpr ?_
  intro i₁ i₂ hlt
  by_cases h₁ : l i₁ = ⊤
  · simp [hA.eq_top_iff.mpr (hA.isRowEchelon.row_eq_zero_of_lt hlt (hA.eq_top_iff.mp h₁))]
  · exact (hA.lt_of_lt_of_ne_top hlt h₁).le

end IsPivotedBy

/-- The map-structural characterisation of pivots. This is useful for proving that
a matrix is in row echelon form. -/
theorem isPivotedBy_iff [PartialOrder m] [LinearOrder n] :
    A.IsPivotedBy l ↔
      Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧ ∀ i : m,
        (∀ j : n, (j : WithTop n) < l i → A i j = 0) ∧ ∀ c : n, l i = c → A i c ≠ 0 := by
  refine ⟨fun hA => ⟨hA.monotone, hA.strictMonoOn, hA.isPivotEntry⟩, ?_⟩
  refine fun ⟨hmono, hstrict, hlead⟩ ↦ ⟨fun i₁ i₂ hlt j₂ hz ↦ (hlead i₂).1 j₂ ?_, hlead⟩
  rcases eq_or_ne (l i₂) ⊤ with h₂ | h₂
  · rw [h₂]
    exact WithTop.coe_lt_top j₂
  · have h₁ : l i₁ ≠ ⊤ := fun ht => h₂ (top_le_iff.mp (ht.symm.le.trans (hmono hlt.le)))
    obtain ⟨c₁, hc₁⟩ := WithTop.ne_top_iff_exists.mp h₁
    have hj : (j₂ : WithTop n) ≤ c₁ :=
      WithTop.coe_le_coe.mpr <| le_of_not_gt fun hgt => (hlead i₁).2 c₁ hc₁.symm (hz c₁ hgt)
    exact lt_of_le_of_lt (hj.trans hc₁.le) (hstrict h₁ h₂ hlt)

/-- A variant of `isPivotedBy_iff` phrased with `Matrix.IsLeadingEntry`. -/
theorem isPivotedBy_iff' [PartialOrder m] [LinearOrder n] :
    A.IsPivotedBy l ↔
      Monotone l ∧ StrictMonoOn l {i | l i ≠ ⊤} ∧
        ∀ i : m, (l i = ⊤ ∧ A i = 0) ∨ (∃ c : n, l i = c ∧ A.IsLeadingEntry i c) := by
  rw [isPivotedBy_iff]
  refine and_congr_right' <| and_congr_right' <| forall_congr' fun i => ?_
  cases l i <;> simp [IsLeadingEntry, funext_iff]

end Zero

section Rank

variable [Fintype m] [Fintype n] [LinearOrder m] [LinearOrder n] [CommRing R] [IsDomain R]
  {A : Matrix m n R} {l : m → WithTop n}

namespace IsPivotedBy

theorem rank_eq (hA : A.IsPivotedBy l) : A.rank = #{i | l i ≠ ⊤} := by
  refine le_antisymm (A.rank_le_card_of_support_subset _
    (Function.support_subset_iff'.mpr fun i hi => hA.eq_top_iff.mp (by aesop))) ?_
  let g : {i // l i ≠ ⊤} → n := fun i => (l i.1).untop i.2
  have hlead : ∀ i : {i // l i ≠ ⊤}, A.IsLeadingEntry i.1 (g i) := fun i =>
    hA.isLeadingEntry (WithTop.coe_untop (l i.1) i.2).symm
  have htri : (A.submatrix Subtype.val g).IsUpperTriangular := by
    intro i j hij
    exact (hlead i).1 _ ((WithTop.untop_lt_untop_iff _ _).mpr (hA.strictMonoOn j.2 i.2 hij))
  have hdet : (A.submatrix Subtype.val g).det ≠ 0 := by
    rw [det_of_isUpperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hlead i).2
  calc #{i | l i ≠ ⊤}
      = (A.submatrix Subtype.val g).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_subtype]
    _ ≤ A.rank := rank_submatrix_le A Subtype.val g

end IsPivotedBy

end Rank

/-! ## Decidability -/

section Decidability

variable [Zero R] [DecidableEq R]

instance [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n]
    (A : Matrix m n R) (l : m → WithTop n) : Decidable (A.IsPivotedBy l) :=
  -- instance resolution cannot nest `Fintype.decidableForallFintype` under another binder
  have : DecidablePred fun i : m =>
      (∀ j : n, (j : WithTop n) < l i → A i j = 0) ∧ ∀ c : n, l i = c → A i c ≠ 0 :=
    fun _ => inferInstance
  decidable_of_iff' _ isPivotedBy_iff

end Decidability

end Matrix

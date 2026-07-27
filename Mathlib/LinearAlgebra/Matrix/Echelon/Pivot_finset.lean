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
# Pivots of a matrix, `Finset` formulation (draft)

A standalone parallel of `Pivot.lean` over matrices with general linearly ordered finite
indices, carrying the pivot columns as a `Finset n`. The formulation is relational: `s` is
a pivot set of `A` when `A` is in row echelon form and `s` is characterized as the set of
leading (leftmost nonzero) columns of the rows of `A`. No positional access appears in the
statements.
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : Type*} {R : Type*}

/-! ### Leading entries -/
/- These goes into basic.lean if adopted -/

/-- `c` is the column of the leading nonzero entry of row `i`. -/
def IsLeadingEntry [Zero R] [LT n] (A : Matrix m n R) (i : m) (c : n) : Prop :=
  (∀ j < c, A i j = 0) ∧ A i c ≠ 0

/-- A row has at most one leading entry. Currently unused -/
theorem IsLeadingEntry.unique [Zero R] [LinearOrder n] {A : Matrix m n R} {i : m}
    {c₁ c₂ : n} (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) : c₁ = c₂ :=
  le_antisymm (not_lt.mp fun h => h₂.2 (h₁.1 _ h)) (not_lt.mp fun h => h₁.2 (h₂.1 _ h))

/-- In an echelon matrix, a column is led by at most one row. -/
theorem RowEchelon.isLeadingEntry_row_eq [Zero R] [LinearOrder m] [LT n]
    {A : Matrix m n R} {i₁ i₂ : m} {c : n} (he : A.RowEchelon)
    (h₁ : A.IsLeadingEntry i₁ c) (h₂ : A.IsLeadingEntry i₂ c) : i₁ = i₂ :=
  le_antisymm (not_lt.mp fun hlt => h₁.2 (he hlt h₂.1))
    (not_lt.mp fun hlt => h₂.2 (he hlt h₁.1))

/-- In an echelon matrix, leading columns of lower rows are strictly to the right. -/
theorem RowEchelon.isLeadingEntry_lt [Zero R] [LT m] [LinearOrder n]
    {A : Matrix m n R} {i₁ i₂ : m} {c₁ c₂ : n} (he : A.RowEchelon)
    (h₁ : A.IsLeadingEntry i₁ c₁) (h₂ : A.IsLeadingEntry i₂ c₂) (hlt : i₁ < i₂) :
    c₁ < c₂ :=
  lt_of_not_ge fun hge => h₂.2 (he hlt fun j hj => h₁.1 j (hj.trans_le hge))

/-- In an echelon matrix, rows below a zero row are zero. -/
theorem RowEchelon.row_eq_zero_of_lt [Zero R] [LT m] [LT n] {A : Matrix m n R}
    {i₁ i₂ : m} (he : A.RowEchelon) (hlt : i₁ < i₂) (h0 : A i₁ = 0) : A i₂ = 0 :=
  funext fun _ => he hlt fun j₁ _ => congrFun h0 j₁

/-- Over a well-founded column order, a nonzero row has a leading entry. -/
theorem exists_isLeadingEntry_of_ne_zero [Zero R] [LT n] [WellFoundedLT n]
    {A : Matrix m n R} {i : m} (h : A i ≠ 0) : ∃ c, A.IsLeadingEntry i c := by
  obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {j | A i j ≠ 0} (Function.ne_iff.mp h)
  exact ⟨c, fun j hj => not_not.mp fun hj' => hmin j hj' hj, hc⟩

/-! ### Pivot sets -/

/-- `s` is a pivot set of `A`: the matrix is in row echelon form and `s` is the set of
leading columns of its rows. -/
structure IsPivotFinset [Zero R] [LT m] [LT n] (A : Matrix m n R) (s : Finset n) :
    Prop where
  rowEchelon : A.RowEchelon
  -- a similar design to FilterBases that states a separate iff lemma later.
  mem_iff' : ∀ c : n, c ∈ s ↔ ∃ i, A.IsLeadingEntry i c

theorem IsPivotFinset.mem_iff [Zero R] [LT m] [LT n] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) {c : n} : c ∈ s ↔ ∃ i, A.IsLeadingEntry i c :=
  h.mem_iff' c

theorem IsPivotFinset.rank_le_card [LinearOrder m] [Fintype n] [LinearOrder n]
    [CommSemiring R] [StrongRankCondition R] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) : A.rank ≤ s.card := by
  choose f hf using fun c : s => h.mem_iff.mp c.2
  refine (rank_le_card_of_row_eq_zero A (s.attach.image f) fun i hi => ?_).trans
    (card_image_le.trans_eq card_attach)
  contrapose! hi
  obtain ⟨c, hc⟩ := exists_isLeadingEntry_of_ne_zero hi
  have hcs : c ∈ s := h.mem_iff.mpr ⟨i, hc⟩
  refine mem_image.mpr ⟨⟨c, hcs⟩, mem_attach _ _, ?_⟩
  exact h.rowEchelon.isLeadingEntry_row_eq (hf ⟨c, hcs⟩) hc

theorem IsPivotFinset.card_le_rank [LT m] [Fintype n] [LinearOrder n]
    [CommRing R] [IsDomain R] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) : s.card ≤ A.rank := by
  choose f hf using fun c : s => h.mem_iff.mp c.2
  have htri : (A.submatrix f Subtype.val).BlockTriangular id := fun i j hij =>
    (hf i).1 _ hij
  have hdet : (A.submatrix f Subtype.val).det ≠ 0 := by
    rw [det_of_upperTriangular htri]
    exact prod_ne_zero_iff.mpr fun i _ => (hf i).2
  calc s.card = (A.submatrix f Subtype.val).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_coe]
    _ ≤ A.rank := rank_submatrix_le A f Subtype.val

theorem IsPivotFinset.rank_eq [LinearOrder m] [Fintype n] [LinearOrder n]
    [CommRing R] [IsDomain R] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) : A.rank = s.card :=
  le_antisymm h.rank_le_card h.card_le_rank

theorem rank_mul_eq_right_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
    [CommRing R] [IsDomain R] (A : Matrix m m R) (B : Matrix m n R) (σ : Equiv.Perm m)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) :
    (A * B.submatrix σ id).rank = B.rank := by
  have hdet : A.det ≠ 0 := by
    rw [det_of_lowerTriangular A hA]
    exact prod_ne_zero_iff.mpr fun i _ => hd i
  rw [rank_mul_eq_right_of_det_ne_zero A (B.submatrix σ id) hdet]
  exact rank_submatrix B σ (Equiv.refl n)

theorem IsPivotFinset.rank_eq_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
    [LinearOrder n] [CommRing R] [IsDomain R] {A : Matrix m m R} {B : Matrix m n R}
    {σ : Equiv.Perm m} {s : Finset n} (hpiv : (A * B.submatrix σ id).IsPivotFinset s)
    (hA : A.BlockTriangular toDual) (hd : ∀ i, A i i ≠ 0) : B.rank = s.card := by
  rw [← rank_mul_eq_right_of_lowerTriangular A B σ hA hd, hpiv.rank_eq]

/-! ## Decidability

`IsPivotFinset` and `BlockTriangular` are decidable over a `DecidableEq` ring, so a certified
`(T, σ, s)` computed off-kernel can be checked by `decide +kernel` directly on the matrix.

Note that the fin-set based version requires a bespoke decidability instance, as the
automatically synthesised version perform a lot of redundant `s.sort`.
-/

/-- A relation holds pairwise on the sorted enumeration of a `Finset` iff it holds for every
ordered pair of elements. -/
theorem _root_.Finset.pairwise_sort_iff {α : Type*} [LinearOrder α] {s : Finset α}
    {r : α → α → Prop} :
    (s.sort (· ≤ ·)).Pairwise r ↔ ∀ a₁ ∈ s, ∀ a₂ ∈ s, a₁ < a₂ → r a₁ a₂ := by
  constructor
  · intro hp a₁ h₁ a₂ h₂ hlt
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp ((mem_sort (· ≤ ·)).mpr h₁)
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp ((mem_sort (· ≤ ·)).mpr h₂)
    exact List.pairwise_iff_getElem.mp hp i j hi hj
      (s.sortedLT_sort.getElem_lt_getElem_iff.mp hlt)
  · exact fun h => s.sortedLT_sort.pairwise.imp_of_mem fun ha hb hlt =>
      h _ ((mem_sort _).mp ha) _ ((mem_sort _).mp hb) hlt

/-- A relation holds pairwise on the sorted enumeration of a finite linear order iff it holds
for every ordered pair. -/
theorem _root_.Finset.pairwise_sort_univ_iff {α : Type*} [Fintype α] [LinearOrder α]
    {r : α → α → Prop} :
    ((univ : Finset α).sort (· ≤ ·)).Pairwise r ↔ ∀ ⦃a₁ a₂ : α⦄, a₁ < a₂ → r a₁ a₂ :=
  Finset.pairwise_sort_iff.trans
    ⟨fun h _ _ hlt => h _ (mem_univ _) _ (mem_univ _) hlt, fun h _ _ _ _ hlt => h hlt⟩

/-- The leading column of row `r`, or `none` for a zero row. -/
def leadingCol [Zero R] [DecidableEq R] [Fintype n] [LinearOrder n] (A : Matrix m n R)
    (r : m) : Option n :=
  (univ.filter fun j => A r j ≠ 0).min

theorem leadingCol_eq_some_iff [Zero R] [DecidableEq R] [Fintype n] [LinearOrder n]
    {A : Matrix m n R} {r : m} {c : n} :
    leadingCol A r = some c ↔ A.IsLeadingEntry r c := by
  constructor
  · intro h
    replace h : (univ.filter fun j => A r j ≠ 0).min = (c : WithTop n) := h
    refine ⟨fun j hj => ?_, (mem_filter.mp (mem_of_min h)).2⟩
    by_contra hj'
    have hjmem : j ∈ univ.filter fun j => A r j ≠ 0 := mem_filter.mpr ⟨mem_univ _, hj'⟩
    exact absurd (min_le_of_eq hjmem h) (not_le.mpr hj)
  · intro hlead
    change (univ.filter fun j => A r j ≠ 0).min = (c : WithTop n)
    refine le_antisymm (min_le (mem_filter.mpr ⟨mem_univ _, hlead.2⟩)) (Finset.le_min ?_)
    exact fun b hb => WithTop.coe_le_coe.mpr
      (not_lt.mp fun hbc => (mem_filter.mp hb).2 (hlead.1 b hbc))

theorem leadingCol_eq_none_iff [Zero R] [DecidableEq R] [Fintype n] [LinearOrder n]
    {A : Matrix m n R} {r : m} : leadingCol A r = none ↔ A r = 0 :=
  Finset.min_eq_top.trans <| by simp [filter_eq_empty_iff, funext_iff]

theorem mem_filterMap_leadingCol [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] {A : Matrix m n R} {c : n} :
    c ∈ ((univ : Finset m).sort (· ≤ ·)).filterMap (leadingCol A) ↔
      ∃ i, A.IsLeadingEntry i c := by
  simp [leadingCol_eq_some_iff]

/-- The staircase relation between the optional leading columns of two rows in order:
leading columns strictly increase, and no nonzero row follows a zero row. -/
def LeadStep [LT n] : Option n → Option n → Prop
  | some c₁, some c₂ => c₁ < c₂
  | some _, none => True
  | none, o₂ => o₂ = none

instance [LT n] [DecidableLT n] : DecidableRel (LeadStep (n := n))
  | some c₁, some c₂ => inferInstanceAs (Decidable (c₁ < c₂))
  | some _, none => .isTrue trivial
  | none, none => .isTrue rfl
  | none, some _ => .isFalse (Option.some_ne_none _)

/-- A matrix is in row echelon form iff the optional leading columns of every ordered pair of
rows satisfy the staircase relation. -/
theorem rowEchelon_iff_leadStep [Zero R] [DecidableEq R] [LT m] [Fintype n] [LinearOrder n]
    {A : Matrix m n R} :
    A.RowEchelon ↔ ∀ ⦃i₁ i₂ : m⦄, i₁ < i₂ → LeadStep (leadingCol A i₁) (leadingCol A i₂) := by
  constructor
  · intro hre i₁ i₂ hlt
    cases h₁ : leadingCol A i₁ with
    | none =>
      exact leadingCol_eq_none_iff.mpr
        (hre.row_eq_zero_of_lt hlt (leadingCol_eq_none_iff.mp h₁))
    | some c₁ =>
      cases h₂ : leadingCol A i₂ with
      | none => trivial
      | some c₂ =>
        exact hre.isLeadingEntry_lt (leadingCol_eq_some_iff.mp h₁)
          (leadingCol_eq_some_iff.mp h₂) hlt
  · intro hstep i₁ i₂ hlt j₂ hz
    cases h₂ : leadingCol A i₂ with
    | none => exact congrFun (leadingCol_eq_none_iff.mp h₂) j₂
    | some c₂ =>
      have hstep' := hstep hlt
      cases h₁ : leadingCol A i₁ with
      | none => rw [h₁, h₂] at hstep'; exact absurd hstep' (Option.some_ne_none c₂)
      | some c₁ =>
        rw [h₁, h₂] at hstep'
        have hlead₁ := leadingCol_eq_some_iff.mp h₁
        have hlead₂ := leadingCol_eq_some_iff.mp h₂
        have hle : ¬ c₁ < j₂ := fun hc => hlead₁.2 (hz _ hc)
        exact hlead₂.1 _ (lt_of_le_of_lt (not_lt.mp hle) hstep')

/-- Decision procedure for `IsPivotFinset`: compute the leading column of each row once,
then check the staircase relation on the rows in order and compare the leading columns
with the sorted pivot set. -/
def isPivotFinsetB [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m] [Fintype n]
    [LinearOrder n] (A : Matrix m n R) (s : Finset n) : Bool :=
  let leads := ((univ : Finset m).sort (· ≤ ·)).map (leadingCol A)
  decide (leads.Pairwise LeadStep) && decide (leads.filterMap id = s.sort (· ≤ ·))

theorem isPivotFinsetB_iff [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m] [Fintype n]
    [LinearOrder n] (A : Matrix m n R) (s : Finset n) :
    isPivotFinsetB A s = true ↔ A.IsPivotFinset s := by
  rw [isPivotFinsetB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.filterMap_map, Function.id_comp,
    List.pairwise_map]
  constructor
  · rintro ⟨hpair, heq⟩
    refine ⟨rowEchelon_iff_leadStep.mpr (Finset.pairwise_sort_univ_iff.mp hpair),
      fun c => (mem_sort _).symm.trans (heq ▸ mem_filterMap_leadingCol)⟩
  · rintro ⟨hre, hmem⟩
    have hstep := rowEchelon_iff_leadStep.mp hre
    refine ⟨Finset.pairwise_sort_univ_iff.mpr hstep, ?_⟩
    have hsorted : (((univ : Finset m).sort (· ≤ ·)).filterMap (leadingCol A)).SortedLT :=
      ((Finset.pairwise_sort_univ_iff.mpr hstep).filterMap (leadingCol A)
        fun _ _ h _ hb _ hb' => by rw [hb, hb'] at h; exact h).sortedLT
    exact hsorted.eq_of_mem_iff (sortedLT_sort _) fun c =>
      mem_filterMap_leadingCol.trans ((hmem c).symm.trans (mem_sort _).symm)

instance decidableIsPivotFinset [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] (A : Matrix m n R) (s : Finset n) :
    Decidable (A.IsPivotFinset s) :=
  decidable_of_iff _ (isPivotFinsetB_iff A s)

end Matrix

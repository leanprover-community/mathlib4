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
    {c₁ c₂ : n} (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) : c₁ = c₂ := by
  rcases lt_trichotomy c₁ c₂ with hlt | heq | hlt
  · exact absurd (h₂.1 c₁ hlt) h₁.2
  · exact heq
  · exact absurd (h₁.1 c₂ hlt) h₂.2

/-- In an echelon matrix, a column is led by at most one row. -/
theorem RowEchelon.isLeadingEntry_row_eq [Zero R] [LinearOrder m] [LT n]
    {A : Matrix m n R} {i₁ i₂ : m} {c : n} (he : A.RowEchelon)
    (h₁ : A.IsLeadingEntry i₁ c) (h₂ : A.IsLeadingEntry i₂ c) : i₁ = i₂ := by
  rcases lt_trichotomy i₁ i₂ with hlt | heq | hlt
  · exact absurd (he hlt h₁.1) h₂.2
  · exact heq
  · exact absurd (he hlt h₂.1) h₁.2

/-- In an echelon matrix, leading columns of lower rows are strictly to the right. -/
theorem RowEchelon.isLeadingEntry_lt [Zero R] [LT m] [LinearOrder n]
    {A : Matrix m n R} {i₁ i₂ : m} {c₁ c₂ : n} (he : A.RowEchelon)
    (h₁ : A.IsLeadingEntry i₁ c₁) (h₂ : A.IsLeadingEntry i₂ c₂) (hlt : i₁ < i₂) :
    c₁ < c₂ := by
  by_contra hle
  exact h₂.2 (he hlt fun j hj => h₁.1 j (lt_of_lt_of_le hj (not_lt.mp hle)))

/-- In an echelon matrix, rows below a zero row are zero. -/
theorem RowEchelon.row_eq_zero_of_lt [Zero R] [LT m] [LT n] {A : Matrix m n R}
    {i₁ i₂ : m} (he : A.RowEchelon) (hlt : i₁ < i₂) (h0 : A i₁ = 0) : A i₂ = 0 := by
  funext j
  simp [he hlt (fun j _ => (congrFun h0 j))]

/-- Over a finite linear order of columns, a nonzero row has a leading entry. -/
theorem exists_isLeadingEntry_of_ne_zero [Zero R] [Finite n] [LinearOrder n]
    {A : Matrix m n R} {i : m} (h : A i ≠ 0) : ∃ c, A.IsLeadingEntry i c := by
  cases nonempty_fintype n
  -- todo: check mathlib's policy on classical
  classical
  have hne : (univ.filter fun j => A i j ≠ 0).Nonempty := by
    rcases Function.ne_iff.mp h with ⟨j, hj⟩
    exact ⟨j, mem_filter.mpr ⟨mem_univ _, by simpa using hj⟩⟩
  refine ⟨(univ.filter fun j => A i j ≠ 0).min' hne, fun j hj => ?_, ?_⟩
  · by_contra hj'
    exact absurd
      (min'_le _ j (mem_filter.mpr ⟨mem_univ _, hj'⟩))
      (not_le.mpr hj)
  · exact (mem_filter.mp ((univ.filter fun j => A i j ≠ 0).min'_mem hne)).2

/-! ### Pivot sets -/

/-- `s` is a pivot set of `A`: the matrix is in row echelon form and `s` is the set of
leading columns of its rows. -/
structure IsPivotFinset [Zero R] [LT m] [LT n] (A : Matrix m n R) (s : Finset n) :
    Prop where
  rowEchelon : A.RowEchelon
  mem_iff : ∀ c, c ∈ s ↔ ∃ i, A.IsLeadingEntry i c

theorem IsPivotFinset.rank_le_card [LinearOrder m] [Fintype n] [LinearOrder n]
    [CommSemiring R] [StrongRankCondition R] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) : A.rank ≤ s.card := by
  choose f hf using fun c : ↥s => (h.mem_iff _).mp c.2
  refine (rank_le_card_of_row_eq_zero A (s.attach.image f) fun i hi => ?_).trans
    (card_image_le.trans_eq card_attach)
  by_contra h0
  obtain ⟨c, hc⟩ := exists_isLeadingEntry_of_ne_zero h0
  have hcs : c ∈ s := (h.mem_iff _).mpr ⟨i, hc⟩
  exact hi (mem_image.mpr ⟨⟨c, hcs⟩, mem_attach _ _,
    h.rowEchelon.isLeadingEntry_row_eq (hf ⟨c, hcs⟩) hc⟩)

theorem IsPivotFinset.card_le_rank [LT m] [Fintype n] [LinearOrder n]
    [CommRing R] [IsDomain R] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) : s.card ≤ A.rank := by
  choose f hf using fun c : ↥s => (h.mem_iff _).mp c.2
  have htri : (A.submatrix f Subtype.val).BlockTriangular id := fun a b hab =>
    (hf a).1 _ hab
  have hdet : (A.submatrix f Subtype.val).det ≠ 0 := by
    rw [det_of_upperTriangular htri]
    exact prod_ne_zero_iff.mpr fun a _ => (hf a).2
  calc (s.card : ℕ) = (A.submatrix f Subtype.val).rank := by
        rw [rank_of_det_ne_zero hdet, Fintype.card_coe]
    _ ≤ A.rank := rank_submatrix_le A _ _

theorem IsPivotFinset.rank_eq [LinearOrder m] [Fintype n] [LinearOrder n]
    [CommRing R] [IsDomain R] {A : Matrix m n R} {s : Finset n}
    (h : A.IsPivotFinset s) : A.rank = s.card :=
  le_antisymm h.rank_le_card h.card_le_rank

lemma rank_mul_eq_right_of_lowerTriangular [Fintype m] [LinearOrder m] [Fintype n]
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

/-- A relation holds pairwise on the sorted enumeration of a finite linear order iff it holds
for every ordered pair. -/
theorem _root_.Finset.pairwise_sort_univ_iff {α : Type*} [Fintype α] [LinearOrder α]
    {r : α → α → Prop} :
    ((univ : Finset α).sort (· ≤ ·)).Pairwise r ↔ ∀ ⦃a₁ a₂ : α⦄, a₁ < a₂ → r a₁ a₂ := by
  constructor
  · intro hp a₁ a₂ hlt
    have hsub : List.Sublist [a₁, a₂] ((univ : Finset α).sort (· ≤ ·)) :=
      List.sublist_of_subperm_of_sortedLE
        ((List.nodup_cons.mpr ⟨by simp [hlt.ne], List.nodup_singleton _⟩).subperm
          fun a _ => (mem_sort _).mpr (mem_univ a))
        (List.sortedLE_iff_pairwise.mpr (by simp [hlt.le]))
        (List.sortedLE_iff_pairwise.mpr (pairwise_sort _ _))
    exact List.pairwise_iff_forall_sublist.mp hp hsub
  · exact fun h => (List.sortedLT_iff_pairwise.mp (sortedLT_sort _)).imp fun hlt => h hlt

/-- The leading column of row `r`, or `none` for a zero row. -/
def leadingCol [Zero R] [DecidableEq R] [Fintype n] [LinearOrder n] (A : Matrix m n R)
    (r : m) : Option n :=
  if h : (univ.filter fun j => A r j ≠ 0).Nonempty then
    some ((univ.filter fun j => A r j ≠ 0).min' h)
  else
    none

theorem leadingCol_eq_some_iff [Zero R] [DecidableEq R] [Fintype n] [LinearOrder n]
    {A : Matrix m n R} {r : m} {c : n} :
    leadingCol A r = some c ↔ A.IsLeadingEntry r c := by
  constructor
  · intro h
    rw [leadingCol] at h
    split at h
    · rename_i hne
      obtain rfl : (univ.filter fun j => A r j ≠ 0).min' hne = c :=
        Option.some_injective _ h
      refine ⟨fun j hj => ?_, ?_⟩
      · by_contra hj'
        exact absurd
          (min'_le _ j (mem_filter.mpr ⟨mem_univ _, hj'⟩))
          (not_le.mpr hj)
      · exact (mem_filter.mp
          ((univ.filter fun j => A r j ≠ 0).min'_mem hne)).2
    · exact absurd h (by simp)
  · intro hlead
    have hcmem : c ∈ univ.filter fun j => A r j ≠ 0 :=
      mem_filter.mpr ⟨mem_univ _, hlead.2⟩
    have hne : (univ.filter fun j => A r j ≠ 0).Nonempty := ⟨c, hcmem⟩
    rw [leadingCol, dif_pos hne]
    have hle := min'_le _ c hcmem
    have hmem := (mem_filter.mp
      ((univ.filter fun j => A r j ≠ 0).min'_mem hne)).2
    rcases eq_or_lt_of_le hle with heq | hlt
    · rw [heq]
    · exact absurd (hlead.1 _ hlt) hmem

theorem leadingCol_eq_none_iff [Zero R] [DecidableEq R] [Fintype n] [LinearOrder n]
    {A : Matrix m n R} {r : m} : leadingCol A r = none ↔ A r = 0 := by
  constructor
  · intro h
    funext j
    change A r j = 0
    by_contra hj
    rw [leadingCol, dif_pos ⟨j, mem_filter.mpr ⟨mem_univ _, hj⟩⟩] at h
    exact absurd h (by simp)
  · intro h0
    rw [leadingCol, dif_neg]
    rintro ⟨j, hj⟩
    exact (mem_filter.mp hj).2 (congrFun h0 j)

theorem mem_filterMap_leadingCol [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] {A : Matrix m n R} {c : n} :
    c ∈ ((univ : Finset m).sort (· ≤ ·)).filterMap (leadingCol A) ↔
      ∃ i, A.IsLeadingEntry i c := by
  simp [List.mem_filterMap, leadingCol_eq_some_iff]

/-- The staircase relation between the optional leading columns of two rows in order:
leading columns strictly increase, and no nonzero row follows a zero row. -/
def LeadStep [LT n] : Option n → Option n → Prop
  | some c₁, some c₂ => c₁ < c₂
  | some _, none => True
  | none, o₂ => o₂ = none

instance [LinearOrder n] : DecidableRel (LeadStep (n := n)) := fun o₁ o₂ => by
  cases o₁ <;> cases o₂ <;> simp only [LeadStep] <;> infer_instance

/-- A matrix is in row echelon form iff the optional leading columns of every ordered pair of
rows satisfy the staircase relation. -/
theorem rowEchelon_iff_leadStep [Zero R] [DecidableEq R] [LT m] [Fintype n] [LinearOrder n]
    {A : Matrix m n R} :
    A.RowEchelon ↔ ∀ ⦃i₁ i₂ : m⦄, i₁ < i₂ → LeadStep (leadingCol A i₁) (leadingCol A i₂) := by
  constructor
  · intro hre i₁ i₂ hlt
    cases h₁ : leadingCol A i₁ with
    | none =>
      change leadingCol A i₂ = none
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
      | none => rw [h₁, h₂] at hstep'; exact absurd hstep' (by simp [LeadStep])
      | some c₁ =>
        rw [h₁, h₂] at hstep'
        have hc₁₂ : c₁ < c₂ := hstep'
        have hlead₁ := leadingCol_eq_some_iff.mp h₁
        have hlead₂ := leadingCol_eq_some_iff.mp h₂
        have hle : ¬ c₁ < j₂ := fun hc => hlead₁.2 (hz _ hc)
        exact hlead₂.1 _ (lt_of_le_of_lt (not_lt.mp hle) hc₁₂)

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
    have hsorted : (((univ : Finset m).sort (· ≤ ·)).filterMap (leadingCol A)).SortedLT := by
      rw [List.sortedLT_iff_pairwise, List.pairwise_filterMap]
      refine Finset.pairwise_sort_univ_iff.mpr fun r₁ r₂ hlt b hb b' hb' => ?_
      have h := hstep hlt
      rw [hb, hb'] at h
      exact h
    exact List.Subset.antisymm_of_sortedLT
      (fun c hc => (mem_sort _).mpr ((hmem c).mpr (mem_filterMap_leadingCol.mp hc)))
      (fun c hc => mem_filterMap_leadingCol.mpr ((hmem c).mp ((mem_sort _).mp hc)))
      hsorted (sortedLT_sort _)

instance decidableIsPivotFinset [Zero R] [DecidableEq R] [Fintype m] [LinearOrder m]
    [Fintype n] [LinearOrder n] (A : Matrix m n R) (s : Finset n) :
    Decidable (A.IsPivotFinset s) :=
  decidable_of_iff _ (isPivotFinsetB_iff A s)

end Matrix

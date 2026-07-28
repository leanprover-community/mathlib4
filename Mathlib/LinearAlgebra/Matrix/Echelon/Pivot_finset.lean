/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.Data.Fintype.Sort
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

## Main definitions

- `Matrix.IsLeadingEntry`: `c` is the leading column of row `i` of `A`.
- `Matrix.IsPivotFinset`: `s` is the set of leading columns of the echelon matrix `A`.

## Main results

- `Matrix.IsPivotFinset.rank_eq`: a matrix with pivot set `s` has rank `s.card`.
- `Matrix.IsPivotFinset.rank_eq_of_lowerTriangular`: the rank of `B`, read off a pivot set
  of `A * B.submatrix σ id` for `A` lower triangular with nonzero diagonal.
- `Matrix.decidableIsPivotFinset`: `IsPivotFinset` is decidable for `Fin`-indexed matrices
  over a `DecidableEq` ring; general linearly ordered finite indices are decided by
  transport along `monoEquivOfFin`.

## Tags

matrix, echelon form, rank, pivot
-/

@[expose] public section

namespace Matrix

open Finset OrderDual

variable {m n : Type*} {R : Type*}

/-! ### Leading entries -/

/-- `c` is the column of the leading nonzero entry of row `i`. -/
def IsLeadingEntry [Zero R] [LT n] (A : Matrix m n R) (i : m) (c : n) : Prop :=
  (∀ j < c, A i j = 0) ∧ A i c ≠ 0

/-- A row has at most one leading entry. -/
theorem IsLeadingEntry.unique [Zero R] [LinearOrder n] {A : Matrix m n R} {i : m}
    {c₁ c₂ : n} (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) : c₁ = c₂ :=
  le_antisymm (not_lt.mp fun h => h₂.2 (h₁.1 _ h)) (not_lt.mp fun h => h₁.2 (h₂.1 _ h))

/-- In an echelon matrix, a column is led by at most one row. -/
theorem RowEchelon.isLeadingEntry_row_unique [Zero R] [LinearOrder m] [LT n]
    {A : Matrix m n R} {i₁ i₂ : m} {c : n} (he : A.RowEchelon)
    (h₁ : A.IsLeadingEntry i₁ c) (h₂ : A.IsLeadingEntry i₂ c) : i₁ = i₂ :=
  le_antisymm (not_lt.mp fun hlt => h₁.2 (he hlt h₂.1))
    (not_lt.mp fun hlt => h₂.2 (he hlt h₁.1))

/-- In an echelon matrix, leading columns of lower rows are strictly to the right. -/
theorem RowEchelon.isLeadingEntry_lt_of_lt [Zero R] [LT m] [LinearOrder n]
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
  exact h.rowEchelon.isLeadingEntry_row_unique (hf ⟨c, hcs⟩) hc

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

A decidability instance is first constructed for specialised `fin n` column index, and later
transported to a general fintype n.
-/

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

instance [Preorder n] : Trans (LeadStep (n := n)) LeadStep LeadStep where
  trans {o₁ o₂ o₃} h₁ h₂ := by
    cases o₁ <;> cases o₂ <;> cases o₃ <;>
      first
        | exact h₁.trans h₂
        | simp_all [LeadStep]

section Decidability

variable [Zero R] [DecidableEq R] {m n : ℕ}

/-- The leading column of row `r`, or `none` for a zero row. -/
def leadingCol (A : Matrix (Fin m) (Fin n) R) (r : Fin m) : Option (Fin n) :=
  (List.finRange n).find? fun j => decide (A r j ≠ 0)

theorem leadingCol_eq_none_iff {A : Matrix (Fin m) (Fin n) R} {r : Fin m} :
    leadingCol A r = none ↔ A r = 0 := by
  rw [leadingCol, List.find?_eq_none]
  simp [funext_iff]

theorem leadingCol_eq_some_iff {A : Matrix (Fin m) (Fin n) R} {r : Fin m} {c : Fin n} :
    leadingCol A r = some c ↔ A.IsLeadingEntry r c := by
  have hmp : ∀ {c' : Fin n}, leadingCol A r = some c' → A.IsLeadingEntry r c' := by
    intro c' h
    obtain ⟨hp, as, bs, heq, hpre⟩ := List.find?_eq_some_iff_append.mp h
    refine ⟨fun j hj => ?_, by simpa using hp⟩
    have hsort : (as ++ c' :: bs).SortedLT := heq ▸ List.sortedLT_finRange n
    have hja : j ∈ as := by
      rcases List.mem_append.mp (heq ▸ List.mem_finRange j) with h' | h'
      · exact h'
      · rcases List.mem_cons.mp h' with rfl | h'
        · exact absurd hj (lt_irrefl _)
        · exact absurd hj ((List.pairwise_cons.mp
            (List.pairwise_append.mp hsort.pairwise).2.1).1 j h').asymm
    simpa using hpre j hja
  refine ⟨hmp, fun hlead => ?_⟩
  cases h : leadingCol A r with
  | none => exact absurd (congrFun (leadingCol_eq_none_iff.mp h) c) hlead.2
  | some c' => exact congrArg some ((hmp h).unique hlead)

theorem mem_filterMap_leadingCol {A : Matrix (Fin m) (Fin n) R} {c : Fin n} :
    c ∈ (List.finRange m).filterMap (leadingCol A) ↔ ∃ i, A.IsLeadingEntry i c := by
  simp [leadingCol_eq_some_iff]

/-- A matrix is in row echelon form iff the optional leading columns of every ordered pair of
rows satisfy the staircase relation. -/
theorem rowEchelon_iff_leadStep {A : Matrix (Fin m) (Fin n) R} :
    A.RowEchelon ↔
      ∀ ⦃i₁ i₂ : Fin m⦄, i₁ < i₂ → LeadStep (leadingCol A i₁) (leadingCol A i₂) := by
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
        exact hre.isLeadingEntry_lt_of_lt (leadingCol_eq_some_iff.mp h₁)
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

/-- A relation holds pairwise on `List.finRange` iff it holds for every ordered pair.

todo: This needs to be moved to the correct file eventually; currently gets a `_root_`
qualifier for now.
-/
theorem _root_.List.pairwise_finRange_iff {r : Fin n → Fin n → Prop} :
    (List.finRange n).Pairwise r ↔ ∀ ⦃a₁ a₂ : Fin n⦄, a₁ < a₂ → r a₁ a₂ := by
  constructor
  · intro hp a₁ a₂ hlt
    have h := List.pairwise_iff_getElem.mp hp a₁ a₂
      (by simp) (by simp) hlt
    simpa using h
  · exact fun h => (List.sortedLT_finRange n).pairwise.imp_of_mem fun _ _ hlt => h hlt

/-- Decision procedure for `IsPivotFinset`: compute the leading column of each row once by an
early-exit search, check the staircase relation between consecutive rows, and compare the
leading columns with the pivot set. -/
def isPivotFinsetB (A : Matrix (Fin m) (Fin n) R) (s : Finset (Fin n)) : Bool :=
  let leads := (List.finRange m).map (leadingCol A)
  decide (leads.IsChain LeadStep) && decide (s = (leads.filterMap id).toFinset)

theorem isPivotFinsetB_iff (A : Matrix (Fin m) (Fin n) R) (s : Finset (Fin n)) :
    isPivotFinsetB A s = true ↔ A.IsPivotFinset s := by
  rw [isPivotFinsetB]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.isChain_iff_pairwise,
    List.filterMap_map, Function.id_comp, List.pairwise_map]
  constructor
  · rintro ⟨hpair, heq⟩
    refine ⟨rowEchelon_iff_leadStep.mpr (List.pairwise_finRange_iff.mp hpair), fun c => ?_⟩
    rw [heq, List.mem_toFinset, mem_filterMap_leadingCol]
  · rintro ⟨hre, hmem⟩
    refine ⟨List.pairwise_finRange_iff.mpr (rowEchelon_iff_leadStep.mp hre), ?_⟩
    ext c
    rw [List.mem_toFinset, mem_filterMap_leadingCol]
    exact hmem c

instance decidableIsPivotFinset (A : Matrix (Fin m) (Fin n) R) (s : Finset (Fin n)) :
    Decidable (A.IsPivotFinset s) :=
  decidable_of_iff _ (isPivotFinsetB_iff A s)

end Decidability

/-! ### Transport to general indices

The relational spec transports along order isomorphisms, so matrices over general linearly
ordered finite indices are decided by reindexing along `monoEquivOfFin` to the `Fin`-indexed
checker.
-/

section Transport

variable [Zero R] {m' n' : Type*} [Preorder n] [Preorder n'] {A : Matrix m n R}

theorem isLeadingEntry_submatrix_iff (f : m' → m) (en : n' ≃o n) {i : m'} {c : n'} :
    (A.submatrix f en).IsLeadingEntry i c ↔ A.IsLeadingEntry (f i) (en c) := by
  constructor
  · rintro ⟨hz, hnz⟩
    refine ⟨fun j hj => ?_, hnz⟩
    simpa using hz (en.symm j) (en.symm.lt_symm_apply.mp hj)
  · rintro ⟨hz, hnz⟩
    exact ⟨fun j hj => hz (en j) (en.lt_iff_lt.mpr hj), hnz⟩

variable [Preorder m] [Preorder m'] (em : m' ≃o m) (en : n' ≃o n)

theorem rowEchelon_submatrix_iff : (A.submatrix em en).RowEchelon ↔ A.RowEchelon := by
  constructor
  · intro h i₁ i₂ hlt j₂ hz
    have key := h (em.symm.lt_iff_lt.mpr hlt) (j₂ := en.symm j₂) fun j₁ hj₁ => by
      simpa using hz (en j₁) (en.lt_symm_apply.mp hj₁)
    simpa using key
  · intro h i₁ i₂ hlt j₂ hz
    change A (em i₂) (en j₂) = 0
    refine h (em.lt_iff_lt.mpr hlt) (j₂ := en j₂) fun j₁ hj₁ => ?_
    simpa using hz (en.symm j₁) (en.symm.lt_symm_apply.mp hj₁)

theorem isPivotFinset_submatrix_iff {s : Finset n} :
    (A.submatrix em en).IsPivotFinset (s.map en.symm.toEquiv.toEmbedding) ↔
      A.IsPivotFinset s := by
  have hmem : ∀ c : n', c ∈ s.map en.symm.toEquiv.toEmbedding ↔ en c ∈ s := fun c => by
    rw [mem_map_equiv]
    exact Iff.rfl
  constructor
  · intro h
    refine ⟨(rowEchelon_submatrix_iff em en).mp h.rowEchelon, fun c => ?_⟩
    have hc := h.mem_iff (c := en.symm c)
    rw [hmem, en.apply_symm_apply] at hc
    rw [hc, em.surjective.exists]
    exact exists_congr fun i => by
      rw [isLeadingEntry_submatrix_iff, en.apply_symm_apply]
  · intro h
    refine ⟨(rowEchelon_submatrix_iff em en).mpr h.rowEchelon, fun c => ?_⟩
    rw [hmem, h.mem_iff, em.surjective.exists]
    exact exists_congr fun i => (isLeadingEntry_submatrix_iff (⇑em) en).symm

end Transport

instance (priority := 100) decidableIsPivotFinsetOfFintype [Zero R] [DecidableEq R]
    [Fintype m] [LinearOrder m] [Fintype n] [LinearOrder n] (A : Matrix m n R)
    (s : Finset n) : Decidable (A.IsPivotFinset s) :=
  decidable_of_iff _
    (isPivotFinset_submatrix_iff (monoEquivOfFin m rfl) (monoEquivOfFin n rfl))

end Matrix

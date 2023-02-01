/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson

! This file was ported from Lean 3 source module combinatorics.young.young_diagram
! leanprover-community/mathlib commit 59694bd07f0a39c5beccba34bd9f413a160782bf
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Order.UpperLower.Basic
import Mathbin.Data.Finset.Preimage

/-!
# Young diagrams

A Young diagram is a finite set of up-left justified boxes:

```text
□□□□□
□□□
□□□
□
```
This Young diagram corresponds to the [5, 3, 3, 1] partition of 12.

We represent it as a lower set in `ℕ × ℕ` in the product partial order. We write `(i, j) ∈ μ`
to say that `(i, j)` (in matrix coordinates) is in the Young diagram `μ`.

## Main definitions

- `young_diagram` : Young diagrams
- `young_diagram.card` : the number of cells in a Young diagram (its *cardinality*)
- `young_diagram.distrib_lattice` : a distributive lattice instance for Young diagrams
  ordered by containment, with `(⊥ : young_diagram)` the empty diagram.
- `young_diagram.row` and `young_diagram.row_len`: rows of a Young diagram and their lengths
- `young_diagram.col` and `young_diagram.col_len`: columns of a Young diagram and their lengths

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). This terminology is used
below, e.g. in `young_diagram.up_left_mem`.

## Tags

Young diagram

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/


open Function

/-- A Young diagram is a finite collection of cells on the `ℕ × ℕ` grid such that whenever
a cell is present, so are all the ones above and to the left of it. Like matrices, an `(i, j)` cell
is a cell in row `i` and column `j`, where rows are enumerated downward and columns rightward.

Young diagrams are modeled as finite sets in `ℕ × ℕ` that are lower sets with respect to the
standard order on products. -/
@[ext]
structure YoungDiagram where
  cells : Finset (ℕ × ℕ)
  IsLowerSet : IsLowerSet (cells : Set (ℕ × ℕ))
#align young_diagram YoungDiagram

namespace YoungDiagram

instance : SetLike YoungDiagram (ℕ × ℕ)
    where
  coe := coe YoungDiagram.cells
  coe_injective' μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]

@[simp]
theorem mem_cells {μ : YoungDiagram} (c : ℕ × ℕ) : c ∈ μ.cells ↔ c ∈ μ :=
  Iff.rfl
#align young_diagram.mem_cells YoungDiagram.mem_cells

@[simp]
theorem mem_mk (c : ℕ × ℕ) (cells) (is_lower_set) :
    c ∈ YoungDiagram.mk cells IsLowerSet ↔ c ∈ cells :=
  Iff.rfl
#align young_diagram.mem_mk YoungDiagram.mem_mk

instance decidableMem (μ : YoungDiagram) : DecidablePred (· ∈ μ) :=
  show DecidablePred (· ∈ μ.cells) by infer_instance
#align young_diagram.decidable_mem YoungDiagram.decidableMem

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left of (i2, j2). -/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2)
    (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
  μ.IsLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell
#align young_diagram.up_left_mem YoungDiagram.up_left_mem

section DistribLattice

@[simp]
theorem cells_subset_iff {μ ν : YoungDiagram} : μ.cells ⊆ ν.cells ↔ μ ≤ ν :=
  Iff.rfl
#align young_diagram.cells_subset_iff YoungDiagram.cells_subset_iff

@[simp]
theorem cells_sSubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν :=
  Iff.rfl
#align young_diagram.cells_ssubset_iff YoungDiagram.cells_sSubset_iff

instance : HasSup YoungDiagram
    where sup μ ν :=
    { cells := μ.cells ∪ ν.cells
      IsLowerSet := by
        rw [Finset.coe_union]
        exact μ.is_lower_set.union ν.is_lower_set }

@[simp]
theorem cells_sup (μ ν : YoungDiagram) : (μ ⊔ ν).cells = μ.cells ∪ ν.cells :=
  rfl
#align young_diagram.cells_sup YoungDiagram.cells_sup

@[simp, norm_cast]
theorem coe_sup (μ ν : YoungDiagram) : ↑(μ ⊔ ν) = (μ ∪ ν : Set (ℕ × ℕ)) :=
  Finset.coe_union _ _
#align young_diagram.coe_sup YoungDiagram.coe_sup

@[simp]
theorem mem_sup {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊔ ν ↔ x ∈ μ ∨ x ∈ ν :=
  Finset.mem_union
#align young_diagram.mem_sup YoungDiagram.mem_sup

instance : HasInf YoungDiagram
    where inf μ ν :=
    { cells := μ.cells ∩ ν.cells
      IsLowerSet := by
        rw [Finset.coe_inter]
        exact μ.is_lower_set.inter ν.is_lower_set }

@[simp]
theorem cells_inf (μ ν : YoungDiagram) : (μ ⊓ ν).cells = μ.cells ∩ ν.cells :=
  rfl
#align young_diagram.cells_inf YoungDiagram.cells_inf

@[simp, norm_cast]
theorem coe_inf (μ ν : YoungDiagram) : ↑(μ ⊓ ν) = (μ ∩ ν : Set (ℕ × ℕ)) :=
  Finset.coe_inter _ _
#align young_diagram.coe_inf YoungDiagram.coe_inf

@[simp]
theorem mem_inf {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊓ ν ↔ x ∈ μ ∧ x ∈ ν :=
  Finset.mem_inter
#align young_diagram.mem_inf YoungDiagram.mem_inf

/-- The empty Young diagram is (⊥ : young_diagram). -/
instance : OrderBot YoungDiagram
    where
  bot :=
    { cells := ∅
      IsLowerSet := fun _ _ _ => False.elim }
  bot_le _ _ := False.elim

@[simp]
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl
#align young_diagram.cells_bot YoungDiagram.cells_bot

@[simp, norm_cast]
theorem coe_bot : ↑(⊥ : YoungDiagram) = (∅ : Set (ℕ × ℕ)) :=
  rfl
#align young_diagram.coe_bot YoungDiagram.coe_bot

@[simp]
theorem not_mem_bot (x : ℕ × ℕ) : x ∉ (⊥ : YoungDiagram) :=
  Finset.not_mem_empty x
#align young_diagram.not_mem_bot YoungDiagram.not_mem_bot

instance : Inhabited YoungDiagram :=
  ⟨⊥⟩

instance : DistribLattice YoungDiagram :=
  Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h => by rwa [YoungDiagram.ext_iff])
    (fun _ _ => rfl) fun _ _ => rfl

end DistribLattice

/-- Cardinality of a Young diagram -/
@[reducible]
protected def card (μ : YoungDiagram) : ℕ :=
  μ.cells.card
#align young_diagram.card YoungDiagram.card

section Transpose

/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. -/
def transpose (μ : YoungDiagram) : YoungDiagram
    where
  cells := (Equiv.prodComm _ _).finsetCongr μ.cells
  IsLowerSet _ _ h :=
    by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.is_lower_set _ hcell
    simp [h]
#align young_diagram.transpose YoungDiagram.transpose

@[simp]
theorem mem_transpose {μ : YoungDiagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.symm ∈ μ := by
  simp [transpose]
#align young_diagram.mem_transpose YoungDiagram.mem_transpose

@[simp]
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ :=
  by
  ext
  simp
#align young_diagram.transpose_transpose YoungDiagram.transpose_transpose

theorem transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose := by
  constructor <;>
    · rintro rfl
      simp
#align young_diagram.transpose_eq_iff_eq_transpose YoungDiagram.transpose_eq_iff_eq_transpose

@[simp]
theorem transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν :=
  by
  rw [transpose_eq_iff_eq_transpose]
  simp
#align young_diagram.transpose_eq_iff YoungDiagram.transpose_eq_iff

-- This is effectively both directions of `transpose_le_iff` below.
protected theorem le_of_transpose_le {μ ν : YoungDiagram} (h_le : μ.transpose ≤ ν) :
    μ ≤ ν.transpose := fun c hc => by
  simp only [mem_transpose]
  apply h_le
  simpa
#align young_diagram.le_of_transpose_le YoungDiagram.le_of_transpose_le

@[simp]
theorem transpose_le_iff {μ ν : YoungDiagram} : μ.transpose ≤ ν.transpose ↔ μ ≤ ν :=
  ⟨fun h => by
    convert YoungDiagram.le_of_transpose_le h
    simp, fun h => by
    convert @YoungDiagram.le_of_transpose_le _ _ _
    simpa⟩
#align young_diagram.transpose_le_iff YoungDiagram.transpose_le_iff

@[mono]
protected theorem transpose_mono {μ ν : YoungDiagram} (h_le : μ ≤ ν) : μ.transpose ≤ ν.transpose :=
  transpose_le_iff.mpr h_le
#align young_diagram.transpose_mono YoungDiagram.transpose_mono

/-- Transposing Young diagrams is an `order_iso`. -/
@[simps]
def transposeOrderIso : YoungDiagram ≃o YoungDiagram :=
  ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩
#align young_diagram.transpose_order_iso YoungDiagram.transposeOrderIso

end Transpose

section Rows

/-! ### Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.row_len`, with the following API:
      1.  `(i, j) ∈ μ ↔ j < μ.row_len i`
      2.  `μ.row i = {i} ×ˢ (finset.range (μ.row_len i))`
      3.  `μ.row_len i = (μ.row i).card`
      4.  `∀ {i1 i2}, i1 ≤ i2 → μ.row_len i2 ≤ μ.row_len i1`

Note: #3 is not convenient for defining `μ.row_len`; instead, `μ.row_len` is defined
as the smallest `j` such that `(i, j) ∉ μ`. -/


/-- The `i`-th row of a Young diagram consists of the cells whose first coordinate is `i`. -/
def row (μ : YoungDiagram) (i : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filterₓ fun c => c.fst = i
#align young_diagram.row YoungDiagram.row

theorem mem_row_iff {μ : YoungDiagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i := by
  simp [row]
#align young_diagram.mem_row_iff YoungDiagram.mem_row_iff

theorem mk_mem_row_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.row i ↔ (i, j) ∈ μ := by simp [row]
#align young_diagram.mk_mem_row_iff YoungDiagram.mk_mem_row_iff

protected theorem exists_not_mem_row (μ : YoungDiagram) (i : ℕ) : ∃ j, (i, j) ∉ μ :=
  by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_not_mem_finset
      (μ.cells.Preimage (Prod.mk i) fun _ _ _ _ h =>
        by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩
#align young_diagram.exists_not_mem_row YoungDiagram.exists_not_mem_row

/-- Length of a row of a Young diagram -/
def rowLen (μ : YoungDiagram) (i : ℕ) : ℕ :=
  Nat.find <| μ.exists_not_mem_row i
#align young_diagram.row_len YoungDiagram.rowLen

theorem mem_iff_lt_rowLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.rowLen i :=
  by
  rw [row_len, Nat.lt_find_iff]
  push_neg
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩
#align young_diagram.mem_iff_lt_row_len YoungDiagram.mem_iff_lt_rowLen

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem row_eq_prod {μ : YoungDiagram} {i : ℕ} : μ.row i = {i} ×ˢ Finset.range (μ.rowLen i) :=
  by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_row_len, and_comm', and_congr_right_iff]
  rintro rfl
  rfl
#align young_diagram.row_eq_prod YoungDiagram.row_eq_prod

theorem rowLen_eq_card (μ : YoungDiagram) {i : ℕ} : μ.rowLen i = (μ.row i).card := by
  simp [row_eq_prod]
#align young_diagram.row_len_eq_card YoungDiagram.rowLen_eq_card

@[mono]
theorem rowLen_anti (μ : YoungDiagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.rowLen i2 ≤ μ.rowLen i1 :=
  by
  by_contra' h_lt
  rw [← lt_self_iff_false (μ.row_len i1)]
  rw [← mem_iff_lt_row_len] at h_lt⊢
  exact μ.up_left_mem hi (by rfl) h_lt
#align young_diagram.row_len_anti YoungDiagram.rowLen_anti

end Rows

section Columns

/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/


/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
def col (μ : YoungDiagram) (j : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filterₓ fun c => c.snd = j
#align young_diagram.col YoungDiagram.col

theorem mem_col_iff {μ : YoungDiagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j := by
  simp [col]
#align young_diagram.mem_col_iff YoungDiagram.mem_col_iff

theorem mk_mem_col_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.col j ↔ (i, j) ∈ μ := by simp [col]
#align young_diagram.mk_mem_col_iff YoungDiagram.mk_mem_col_iff

protected theorem exists_not_mem_col (μ : YoungDiagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells :=
  by
  convert μ.transpose.exists_not_mem_row j
  simp
#align young_diagram.exists_not_mem_col YoungDiagram.exists_not_mem_col

/-- Length of a column of a Young diagram -/
def colLen (μ : YoungDiagram) (j : ℕ) : ℕ :=
  Nat.find <| μ.exists_not_mem_col j
#align young_diagram.col_len YoungDiagram.colLen

@[simp]
theorem colLen_transpose (μ : YoungDiagram) (j : ℕ) : μ.transpose.colLen j = μ.rowLen j := by
  simp [row_len, col_len]
#align young_diagram.col_len_transpose YoungDiagram.colLen_transpose

@[simp]
theorem rowLen_transpose (μ : YoungDiagram) (i : ℕ) : μ.transpose.rowLen i = μ.colLen i := by
  simp [row_len, col_len]
#align young_diagram.row_len_transpose YoungDiagram.rowLen_transpose

theorem mem_iff_lt_colLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.colLen j :=
  by
  rw [← row_len_transpose, ← mem_iff_lt_row_len]
  simp
#align young_diagram.mem_iff_lt_col_len YoungDiagram.mem_iff_lt_colLen

/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
theorem col_eq_prod {μ : YoungDiagram} {j : ℕ} : μ.col j = Finset.range (μ.colLen j) ×ˢ {j} :=
  by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_col_len, and_comm', and_congr_right_iff]
  rintro rfl
  rfl
#align young_diagram.col_eq_prod YoungDiagram.col_eq_prod

theorem colLen_eq_card (μ : YoungDiagram) {j : ℕ} : μ.colLen j = (μ.col j).card := by
  simp [col_eq_prod]
#align young_diagram.col_len_eq_card YoungDiagram.colLen_eq_card

@[mono]
theorem colLen_anti (μ : YoungDiagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.colLen j2 ≤ μ.colLen j1 := by
  convert μ.transpose.row_len_anti j1 j2 hj <;> simp
#align young_diagram.col_len_anti YoungDiagram.colLen_anti

end Columns

section RowLens

/-! ### The list of row lengths of a Young diagram

This section defines `μ.row_lens : list ℕ`, the list of row lengths of a Young diagram `μ`.
  1. `young_diagram.row_lens_sorted` : It is weakly decreasing (`list.sorted (≥)`).
  2. `young_diagram.row_lens_pos` : It is strictly positive.

-/


/-- List of row lengths of a Young diagram -/
def rowLens (μ : YoungDiagram) : List ℕ :=
  (List.range <| μ.colLen 0).map μ.rowLen
#align young_diagram.row_lens YoungDiagram.rowLens

@[simp]
theorem nthLe_rowLens {μ : YoungDiagram} {i : ℕ} {hi : i < μ.rowLens.length} :
    μ.rowLens.nthLe i hi = μ.rowLen i := by simp only [row_lens, List.nthLe_range, List.nthLe_map']
#align young_diagram.nth_le_row_lens YoungDiagram.nthLe_rowLens

@[simp]
theorem length_rowLens {μ : YoungDiagram} : μ.rowLens.length = μ.colLen 0 := by
  simp only [row_lens, List.length_map, List.length_range]
#align young_diagram.length_row_lens YoungDiagram.length_rowLens

theorem rowLens_sorted (μ : YoungDiagram) : μ.rowLens.Sorted (· ≥ ·) :=
  (List.pairwise_le_range _).map _ μ.rowLen_anti
#align young_diagram.row_lens_sorted YoungDiagram.rowLens_sorted

theorem pos_of_mem_rowLens (μ : YoungDiagram) (x : ℕ) (hx : x ∈ μ.rowLens) : 0 < x :=
  by
  rw [row_lens, List.mem_map'] at hx
  obtain ⟨i, hi, rfl : μ.row_len i = x⟩ := hx
  rwa [List.mem_range, ← mem_iff_lt_col_len, mem_iff_lt_row_len] at hi
#align young_diagram.pos_of_mem_row_lens YoungDiagram.pos_of_mem_rowLens

end RowLens

section EquivListRowLens

/-! ### Equivalence between Young diagrams and lists of natural numbers

This section defines the equivalence between Young diagrams `μ` and weakly decreasing lists `w`
of positive natural numbers, corresponding to row lengths of the diagram:
  `young_diagram.equiv_list_row_lens :`
  `young_diagram ≃ {w : list ℕ // w.sorted (≥) ∧ ∀ x ∈ w, 0 < x}`

The two directions are `young_diagram.row_lens` (defined above) and `young_diagram.of_row_lens`.

-/


/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/- ./././Mathport/Syntax/Translate/Expr.lean:177:8: unsupported: ambiguous notation -/
/-- The cells making up a `young_diagram` from a list of row lengths -/
protected def cellsOfRowLens : List ℕ → Finset (ℕ × ℕ)
  | [] => ∅
  | w::ws =>
    ({0} : Finset ℕ) ×ˢ Finset.range w ∪
      (cells_of_row_lens ws).map (Embedding.prodMap ⟨_, Nat.succ_injective⟩ (Embedding.refl ℕ))
#align young_diagram.cells_of_row_lens YoungDiagram.cellsOfRowLens

protected theorem mem_cellsOfRowLens {w : List ℕ} {c : ℕ × ℕ} :
    c ∈ YoungDiagram.cellsOfRowLens w ↔ ∃ h : c.fst < w.length, c.snd < w.nthLe c.fst h :=
  by
  induction w generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp [YoungDiagram.cellsOfRowLens]
  · rcases c with ⟨⟨_, _⟩, _⟩
    · simp
    · simpa [w_ih, -Finset.singleton_product, Nat.succ_lt_succ_iff]
#align young_diagram.mem_cells_of_row_lens YoungDiagram.mem_cellsOfRowLens

/-- Young diagram from a sorted list -/
def ofRowLens (w : List ℕ) (hw : w.Sorted (· ≥ ·)) : YoungDiagram
    where
  cells := YoungDiagram.cellsOfRowLens w
  IsLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 ≤ i2, hj : j1 ≤ j2⟩ hcell
    rw [Finset.mem_coe, YoungDiagram.mem_cellsOfRowLens] at hcell⊢
    obtain ⟨h1, h2⟩ := hcell
    refine' ⟨hi.trans_lt h1, _⟩
    calc
      j1 ≤ j2 := hj
      _ < w.nth_le i2 _ := h2
      _ ≤ w.nth_le i1 _ := _
      
    obtain rfl | h := eq_or_lt_of_le hi
    · rfl
    · apply list.pairwise_iff_nth_le.mp hw _ _ _ h
#align young_diagram.of_row_lens YoungDiagram.ofRowLens

theorem mem_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} {c : ℕ × ℕ} :
    c ∈ ofRowLens w hw ↔ ∃ h : c.fst < w.length, c.snd < w.nthLe c.fst h :=
  YoungDiagram.mem_cellsOfRowLens
#align young_diagram.mem_of_row_lens YoungDiagram.mem_ofRowLens

/-- The number of rows in `of_row_lens w hw` is the length of `w` -/
theorem rowLens_length_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens.length = w.length :=
  by
  simp only [length_row_lens, col_len, Nat.find_eq_iff, mem_cells, mem_of_row_lens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  exact ⟨id, fun n hn => ⟨hn, hpos _ (List.nthLe_mem _ _ hn)⟩⟩
#align young_diagram.row_lens_length_of_row_lens YoungDiagram.rowLens_length_ofRowLens

/-- The length of the `i`th row in `of_row_lens w hw` is the `i`th entry of `w` -/
theorem rowLen_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (i : ℕ) (hi : i < w.length) :
    (ofRowLens w hw).rowLen i = w.nthLe i hi := by
  simp [row_len, Nat.find_eq_iff, mem_of_row_lens, hi]
#align young_diagram.row_len_of_row_lens YoungDiagram.rowLen_ofRowLens

/-- The left_inv direction of the equivalence -/
theorem ofRowLens_to_rowLens_eq_self {μ : YoungDiagram} : ofRowLens _ (rowLens_sorted μ) = μ :=
  by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_of_row_lens, length_row_lens, nth_le_row_lens]
  simpa [← mem_iff_lt_col_len, mem_iff_lt_row_len] using j.zero_le.trans_lt
#align young_diagram.of_row_lens_to_row_lens_eq_self YoungDiagram.ofRowLens_to_rowLens_eq_self

/-- The right_inv direction of the equivalence -/
theorem rowLens_ofRowLens_eq_self {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens = w := by
  ext (i r)
  cases lt_or_ge i w.length
  · simp only [Option.mem_def, ← List.nthLe_eq_iff, h, row_lens_length_of_row_lens hpos]
    revert r
    simpa only [eq_iff_eq_cancel_right, nth_le_row_lens] using row_len_of_row_lens _ h
  · rw [list.nth_eq_none_iff.mpr h, list.nth_eq_none_iff.mpr]
    rwa [row_lens_length_of_row_lens hpos]
#align young_diagram.row_lens_of_row_lens_eq_self YoungDiagram.rowLens_ofRowLens_eq_self

/-- Equivalence between Young diagrams and weakly decreasing lists of positive natural numbers.
A Young diagram `μ` is equivalent to a list of row lengths. -/
@[simps]
def equivListRowLens : YoungDiagram ≃ { w : List ℕ // w.Sorted (· ≥ ·) ∧ ∀ x ∈ w, 0 < x }
    where
  toFun μ := ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv μ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨w, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)
#align young_diagram.equiv_list_row_lens YoungDiagram.equivListRowLens

end EquivListRowLens

end YoungDiagram


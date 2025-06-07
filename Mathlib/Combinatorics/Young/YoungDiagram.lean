/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Prod
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.UpperLower.Basic

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

- `YoungDiagram` : Young diagrams
- `YoungDiagram.card` : the number of cells in a Young diagram (its *cardinality*)
- `YoungDiagram.instDistribLatticeYoungDiagram` : a distributive lattice instance for Young diagrams
  ordered by containment, with `(⊥ : YoungDiagram)` the empty diagram.
- `YoungDiagram.row` and `YoungDiagram.rowLen`: rows of a Young diagram and their lengths
- `YoungDiagram.col` and `YoungDiagram.colLen`: columns of a Young diagram and their lengths

## Notation

In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
means (i1, j1) is weakly up-and-left of (i2, j2). This terminology is used
below, e.g. in `YoungDiagram.up_left_mem`.

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
  /-- A finite set which represents a finite collection of cells on the `ℕ × ℕ` grid. -/
  cells : Finset (ℕ × ℕ)
  /-- Cells are up-left justified, witnessed by the fact that `cells` is a lower set in `ℕ × ℕ`. -/
  isLowerSet : IsLowerSet (cells : Set (ℕ × ℕ))

namespace YoungDiagram

instance : SetLike YoungDiagram (ℕ × ℕ) where
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11215): TODO: figure out how to do this correctly
  coe y := y.cells
  coe_injective' μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]

@[simp]
theorem mem_cells {μ : YoungDiagram} (c : ℕ × ℕ) : c ∈ μ.cells ↔ c ∈ μ :=
  Iff.rfl

@[simp]
theorem mem_mk (c : ℕ × ℕ) (cells) (isLowerSet) :
    c ∈ YoungDiagram.mk cells isLowerSet ↔ c ∈ cells :=
  Iff.rfl

instance decidableMem (μ : YoungDiagram) : DecidablePred (· ∈ μ) :=
  inferInstanceAs (DecidablePred (· ∈ μ.cells))

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left of (i2, j2). -/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2)
    (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
  μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell

section DistribLattice

@[simp]
theorem cells_subset_iff {μ ν : YoungDiagram} : μ.cells ⊆ ν.cells ↔ μ ≤ ν :=
  Iff.rfl

@[simp]
theorem cells_ssubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν :=
  Iff.rfl

instance : Max YoungDiagram where
  max μ ν :=
    { cells := μ.cells ∪ ν.cells
      isLowerSet := by
        rw [Finset.coe_union]
        exact μ.isLowerSet.union ν.isLowerSet }

@[simp]
theorem cells_sup (μ ν : YoungDiagram) : (μ ⊔ ν).cells = μ.cells ∪ ν.cells :=
  rfl

@[simp, norm_cast]
theorem coe_sup (μ ν : YoungDiagram) : ↑(μ ⊔ ν) = (μ ∪ ν : Set (ℕ × ℕ)) :=
  Finset.coe_union _ _

@[simp]
theorem mem_sup {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊔ ν ↔ x ∈ μ ∨ x ∈ ν :=
  Finset.mem_union

instance : Min YoungDiagram where
  min μ ν :=
    { cells := μ.cells ∩ ν.cells
      isLowerSet := by
        rw [Finset.coe_inter]
        exact μ.isLowerSet.inter ν.isLowerSet }

@[simp]
theorem cells_inf (μ ν : YoungDiagram) : (μ ⊓ ν).cells = μ.cells ∩ ν.cells :=
  rfl

@[simp, norm_cast]
theorem coe_inf (μ ν : YoungDiagram) : ↑(μ ⊓ ν) = (μ ∩ ν : Set (ℕ × ℕ)) :=
  Finset.coe_inter _ _

@[simp]
theorem mem_inf {μ ν : YoungDiagram} {x : ℕ × ℕ} : x ∈ μ ⊓ ν ↔ x ∈ μ ∧ x ∈ ν :=
  Finset.mem_inter

/-- The empty Young diagram is (⊥ : young_diagram). -/
instance : OrderBot YoungDiagram where
  bot :=
    { cells := ∅
      isLowerSet := by
        intros a b _ h
        simp only [Finset.coe_empty, Set.mem_empty_iff_false]
        simp only [Finset.coe_empty, Set.mem_empty_iff_false] at h }
  bot_le _ _ := by
    intro y
    simp only [mem_mk, Finset.notMem_empty] at y

@[simp]
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl

@[simp]
theorem notMem_bot (x : ℕ × ℕ) : x ∉ (⊥ : YoungDiagram) :=
  Finset.notMem_empty x

@[deprecated (since := "2025-05-23")] alias not_mem_bot := notMem_bot

@[norm_cast]
theorem coe_bot : (⊥ : YoungDiagram) = (∅ : Set (ℕ × ℕ)) := by
  ext; simp

instance : Inhabited YoungDiagram :=
  ⟨⊥⟩

instance : DistribLattice YoungDiagram :=
  Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h => by rwa [YoungDiagram.ext_iff])
    (fun _ _ => rfl) fun _ _ => rfl

end DistribLattice

/-- Cardinality of a Young diagram -/
protected abbrev card (μ : YoungDiagram) : ℕ :=
  μ.cells.card

section Transpose

/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. -/
def transpose (μ : YoungDiagram) : YoungDiagram where
  cells := (Equiv.prodComm _ _).finsetCongr μ.cells
  isLowerSet _ _ h := by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    intro hcell
    apply μ.isLowerSet _ hcell
    simp [h]

@[simp]
theorem mem_transpose {μ : YoungDiagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.swap ∈ μ := by
  simp [transpose]

@[simp]
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ := by
  ext x
  simp

theorem transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose := by
  constructor <;>
    · rintro rfl
      simp

@[simp]
theorem transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν := by
  rw [transpose_eq_iff_eq_transpose]
  simp

-- This is effectively both directions of `transpose_le_iff` below.
protected theorem le_of_transpose_le {μ ν : YoungDiagram} (h_le : μ.transpose ≤ ν) :
    μ ≤ ν.transpose := fun c hc => by
  simp only [mem_cells, mem_transpose]
  apply h_le
  simpa

@[simp]
theorem transpose_le_iff {μ ν : YoungDiagram} : μ.transpose ≤ ν.transpose ↔ μ ≤ ν :=
  ⟨fun h => by
    convert YoungDiagram.le_of_transpose_le h
    simp, fun h => by
    rw [← transpose_transpose μ] at h
    exact YoungDiagram.le_of_transpose_le h ⟩

@[mono]
protected theorem transpose_mono {μ ν : YoungDiagram} (h_le : μ ≤ ν) : μ.transpose ≤ ν.transpose :=
  transpose_le_iff.mpr h_le

/-- Transposing Young diagrams is an `OrderIso`. -/
@[simps]
def transposeOrderIso : YoungDiagram ≃o YoungDiagram :=
  ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩

end Transpose

section Rows

/-! ### Rows and row lengths of Young diagrams.

This section defines `μ.row` and `μ.rowLen`, with the following API:
      1.  `(i, j) ∈ μ ↔ j < μ.rowLen i`
      2.  `μ.row i = {i} ×ˢ (Finset.range (μ.rowLen i))`
      3.  `μ.rowLen i = (μ.row i).card`
      4.  `∀ {i1 i2}, i1 ≤ i2 → μ.rowLen i2 ≤ μ.rowLen i1`

Note: #3 is not convenient for defining `μ.rowLen`; instead, `μ.rowLen` is defined
as the smallest `j` such that `(i, j) ∉ μ`. -/


/-- The `i`-th row of a Young diagram consists of the cells whose first coordinate is `i`. -/
def row (μ : YoungDiagram) (i : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.fst = i

theorem mem_row_iff {μ : YoungDiagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i := by
  simp [row]

theorem mk_mem_row_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.row i ↔ (i, j) ∈ μ := by simp [row]

protected theorem exists_notMem_row (μ : YoungDiagram) (i : ℕ) : ∃ j, (i, j) ∉ μ := by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_notMem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩

@[deprecated (since := "2025-05-23")]
protected alias exists_not_mem_row := YoungDiagram.exists_notMem_row

/-- Length of a row of a Young diagram -/
def rowLen (μ : YoungDiagram) (i : ℕ) : ℕ :=
  Nat.find <| μ.exists_notMem_row i

theorem mem_iff_lt_rowLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.rowLen i := by
  rw [rowLen, Nat.lt_find_iff]
  push_neg
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩

theorem row_eq_prod {μ : YoungDiagram} {i : ℕ} : μ.row i = {i} ×ˢ Finset.range (μ.rowLen i) := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_rowLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

theorem rowLen_eq_card (μ : YoungDiagram) {i : ℕ} : μ.rowLen i = (μ.row i).card := by
  simp [row_eq_prod]

@[mono]
theorem rowLen_anti (μ : YoungDiagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.rowLen i2 ≤ μ.rowLen i1 := by
  by_contra! h_lt
  rw [← lt_self_iff_false (μ.rowLen i1)]
  rw [← mem_iff_lt_rowLen] at h_lt ⊢
  exact μ.up_left_mem hi (by rfl) h_lt

end Rows

section Columns

/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/


/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
def col (μ : YoungDiagram) (j : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.snd = j

theorem mem_col_iff {μ : YoungDiagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j := by
  simp [col]

theorem mk_mem_col_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.col j ↔ (i, j) ∈ μ := by simp [col]

protected theorem exists_notMem_col (μ : YoungDiagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells := by
  convert μ.transpose.exists_notMem_row j using 1
  simp

@[deprecated (since := "2025-05-23")]
protected alias exists_not_mem_col := YoungDiagram.exists_notMem_col

/-- Length of a column of a Young diagram -/
def colLen (μ : YoungDiagram) (j : ℕ) : ℕ :=
  Nat.find <| μ.exists_notMem_col j

@[simp]
theorem colLen_transpose (μ : YoungDiagram) (j : ℕ) : μ.transpose.colLen j = μ.rowLen j := by
  simp [rowLen, colLen]

@[simp]
theorem rowLen_transpose (μ : YoungDiagram) (i : ℕ) : μ.transpose.rowLen i = μ.colLen i := by
  simp [rowLen, colLen]

theorem mem_iff_lt_colLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.colLen j := by
  rw [← rowLen_transpose, ← mem_iff_lt_rowLen]
  simp

theorem col_eq_prod {μ : YoungDiagram} {j : ℕ} : μ.col j = Finset.range (μ.colLen j) ×ˢ {j} := by
  ext ⟨a, b⟩
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_colLen, and_comm, and_congr_right_iff]
  rintro rfl
  rfl

theorem colLen_eq_card (μ : YoungDiagram) {j : ℕ} : μ.colLen j = (μ.col j).card := by
  simp [col_eq_prod]

@[mono]
theorem colLen_anti (μ : YoungDiagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.colLen j2 ≤ μ.colLen j1 := by
  convert μ.transpose.rowLen_anti j1 j2 hj using 1 <;> simp

end Columns

section RowLens

/-! ### The list of row lengths of a Young diagram

This section defines `μ.rowLens : List ℕ`, the list of row lengths of a Young diagram `μ`.
  1. `YoungDiagram.rowLens_sorted` : It is weakly decreasing (`List.Sorted (· ≥ ·)`).
  2. `YoungDiagram.rowLens_pos` : It is strictly positive.

-/


/-- List of row lengths of a Young diagram -/
def rowLens (μ : YoungDiagram) : List ℕ :=
  (List.range <| μ.colLen 0).map μ.rowLen

@[simp]
theorem get_rowLens {μ : YoungDiagram} {i : Nat} {h : i < μ.rowLens.length} :
    μ.rowLens[i] = μ.rowLen i := by simp only [rowLens, List.getElem_range, List.getElem_map]

@[simp]
theorem length_rowLens {μ : YoungDiagram} : μ.rowLens.length = μ.colLen 0 := by
  simp only [rowLens, List.length_map, List.length_range]

theorem rowLens_sorted (μ : YoungDiagram) : μ.rowLens.Sorted (· ≥ ·) :=
  List.pairwise_le_range.map _ μ.rowLen_anti

theorem pos_of_mem_rowLens (μ : YoungDiagram) (x : ℕ) (hx : x ∈ μ.rowLens) : 0 < x := by
  rw [rowLens, List.mem_map] at hx
  obtain ⟨i, hi, rfl : μ.rowLen i = x⟩ := hx
  rwa [List.mem_range, ← mem_iff_lt_colLen, mem_iff_lt_rowLen] at hi

end RowLens

section EquivListRowLens

/-! ### Equivalence between Young diagrams and lists of natural numbers

This section defines the equivalence between Young diagrams `μ` and weakly decreasing lists `w`
of positive natural numbers, corresponding to row lengths of the diagram:
  `YoungDiagram.equivListRowLens :`
  `YoungDiagram ≃ {w : List ℕ // w.Sorted (· ≥ ·) ∧ ∀ x ∈ w, 0 < x}`

The two directions are `YoungDiagram.rowLens` (defined above) and `YoungDiagram.ofRowLens`.

-/


/-- The cells making up a `YoungDiagram` from a list of row lengths -/
protected def cellsOfRowLens : List ℕ → Finset (ℕ × ℕ)
  | [] => ∅
  | w::ws =>
    ({0} : Finset ℕ) ×ˢ Finset.range w ∪
      (YoungDiagram.cellsOfRowLens ws).map
        (Embedding.prodMap ⟨_, Nat.succ_injective⟩ (Embedding.refl ℕ))

protected theorem mem_cellsOfRowLens {w : List ℕ} {c : ℕ × ℕ} :
    c ∈ YoungDiagram.cellsOfRowLens w ↔ ∃ h : c.fst < w.length, c.snd < w[c.fst] := by
  induction w generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp [YoungDiagram.cellsOfRowLens]
  · rcases c with ⟨⟨_, _⟩, _⟩ <;> simp_all

/-- Young diagram from a sorted list -/
def ofRowLens (w : List ℕ) (hw : w.Sorted (· ≥ ·)) : YoungDiagram where
  cells := YoungDiagram.cellsOfRowLens w
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 ≤ i2, hj : j1 ≤ j2⟩ hcell
    rw [Finset.mem_coe, YoungDiagram.mem_cellsOfRowLens] at hcell ⊢
    obtain ⟨h1, h2⟩ := hcell
    refine ⟨hi.trans_lt h1, ?_⟩
    calc
      j1 ≤ j2 := hj
      _ < w[i2]  := h2
      _ ≤ w[i1] := by
        obtain rfl | h := eq_or_lt_of_le hi
        · rfl
        · exact List.pairwise_iff_get.mp hw _ _ h

theorem mem_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} {c : ℕ × ℕ} :
    c ∈ ofRowLens w hw ↔ ∃ h : c.fst < w.length, c.snd < w[c.fst] :=
  YoungDiagram.mem_cellsOfRowLens

/-- The number of rows in `ofRowLens w hw` is the length of `w` -/
theorem rowLens_length_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens.length = w.length := by
  simp only [length_rowLens, colLen, Nat.find_eq_iff, mem_cells, mem_ofRowLens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  exact ⟨not_false, fun n hn => ⟨hn, hpos _ (List.getElem_mem hn)⟩⟩

/-- The length of the `i`th row in `ofRowLens w hw` is the `i`th entry of `w` -/
theorem rowLen_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (i : Fin w.length) :
    (ofRowLens w hw).rowLen i = w[i] := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens]

/-- The left_inv direction of the equivalence -/
theorem ofRowLens_to_rowLens_eq_self {μ : YoungDiagram} : ofRowLens _ (rowLens_sorted μ) = μ := by
  ext ⟨i, j⟩
  simp only [mem_cells, mem_ofRowLens, length_rowLens, get_rowLens]
  simpa [← mem_iff_lt_colLen, mem_iff_lt_rowLen] using j.zero_le.trans_lt

/-- The right_inv direction of the equivalence -/
theorem rowLens_ofRowLens_eq_self {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens = w :=
  List.ext_get (rowLens_length_ofRowLens hpos) fun i h₁ h₂ =>
    (get_rowLens (h := h₁)).trans <| rowLen_ofRowLens ⟨i, h₂⟩

/-- Equivalence between Young diagrams and weakly decreasing lists of positive natural numbers.
A Young diagram `μ` is equivalent to a list of row lengths. -/
@[simps]
def equivListRowLens : YoungDiagram ≃ { w : List ℕ // w.Sorted (· ≥ ·) ∧ ∀ x ∈ w, 0 < x } where
  toFun μ := ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv _ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨_, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)

end EquivListRowLens

end YoungDiagram

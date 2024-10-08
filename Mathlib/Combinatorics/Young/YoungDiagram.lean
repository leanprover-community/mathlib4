/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Multiset
import Mathlib.Combinatorics.Enumerative.Partition

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
  -- Porting note (#11215): TODO: figure out how to do this correctly
  coe := fun y => y.cells
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

instance : Sup YoungDiagram where
  sup μ ν :=
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

instance : Inf YoungDiagram where
  inf μ ν :=
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
    simp only [mem_mk, Finset.not_mem_empty] at y

@[simp]
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl

-- Porting note: removed `↑`, added `.cells` and changed proof
-- @[simp] -- Porting note (#10618): simp can prove this
@[norm_cast]
theorem coe_bot : (⊥ : YoungDiagram).cells = (∅ : Set (ℕ × ℕ)) := by
  refine Set.eq_of_subset_of_subset ?_ ?_
  · intros x h
    simp? [mem_mk, Finset.coe_empty, Set.mem_empty_iff_false] at h says
      simp only [cells_bot, Finset.coe_empty, Set.mem_empty_iff_false] at h
  · simp only [cells_bot, Finset.coe_empty, Set.empty_subset]

@[simp]
theorem not_mem_bot (x : ℕ × ℕ) : x ∉ (⊥ : YoungDiagram) :=
  Finset.not_mem_empty x

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

protected theorem exists_not_mem_row (μ : YoungDiagram) (i : ℕ) : ∃ j, (i, j) ∉ μ := by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_not_mem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  exact ⟨j, hj⟩

/-- Length of a row of a Young diagram -/
def rowLen (μ : YoungDiagram) (i : ℕ) : ℕ :=
  Nat.find <| μ.exists_not_mem_row i

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

protected theorem exists_not_mem_col (μ : YoungDiagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells := by
  convert μ.transpose.exists_not_mem_row j using 1
  simp

/-- Length of a column of a Young diagram -/
def colLen (μ : YoungDiagram) (j : ℕ) : ℕ :=
  Nat.find <| μ.exists_not_mem_col j

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
  (List.pairwise_le_range _).map _ μ.rowLen_anti

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
  induction' w with w_hd w_tl w_ih generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  · simp [YoungDiagram.cellsOfRowLens]
  · rcases c with ⟨⟨_, _⟩, _⟩
    · simp
    -- Porting note: was `simpa`
    · simp [w_ih, -Finset.singleton_product, Nat.succ_lt_succ_iff]

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
  exact ⟨not_false, fun n hn => ⟨hn, hpos _ (List.getElem_mem _ _ hn)⟩⟩

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

section Partition

/-! ### Partitions

This section defines `YoungDiagram.ofPartition`, which constructs Young diagrams corresponding to
partitions of natural numbers.

-/

def length (μ : YoungDiagram) : ℕ := μ.colLen 0

lemma rows_disjoint (μ : YoungDiagram) : Set.PairwiseDisjoint (Finset.range μ.length) μ.row := by
  intro i _ j _ hij s hsi hsj x hx
  rw [← (mem_row_iff.mp (hsi hx)).right, ← (mem_row_iff.mp (hsj hx)).right] at hij
  contradiction

theorem is_disjoint_union_rows (μ : YoungDiagram) : μ.cells
    = Finset.disjiUnion (Finset.range μ.length) μ.row (rows_disjoint μ) := by
  ext ⟨i, j⟩
  simp only [mem_cells, Finset.disjiUnion_eq_biUnion, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · intro h
    use i
    constructor
    · exact mem_iff_lt_colLen.mp (up_left_mem μ (le_refl i) (zero_le j) h)
    · exact mem_row_iff.mpr ⟨h, rfl⟩
  · intro ⟨a, ha⟩
    exact (mem_row_iff.mp ha.2).1

def toPartition (μ : YoungDiagram) : Nat.Partition μ.card where
  parts := (Finset.range μ.length).val.map μ.rowLen
  parts_pos := by
    intro i hi
    simp only [Multiset.mem_map, Finset.mem_val] at hi
    obtain ⟨j, hj, rfl⟩ := hi
    rw [Finset.mem_range, YoungDiagram.length, ← mem_iff_lt_colLen] at hj
    exact mem_iff_lt_rowLen.mp hj
  parts_sum := by
    simp_rw [YoungDiagram.card, rowLen_eq_card, is_disjoint_union_rows]
    exact Eq.symm (Finset.card_disjiUnion (Finset.range μ.length) μ.row (rows_disjoint μ))

def cells_ofPartition {n : ℕ} (p : Nat.Partition n) : Set (ℕ × ℕ) :=
  { (i, j) : ℕ × ℕ | i < Multiset.card (Multiset.filter (fun s ↦ (s > j)) p.parts) }

lemma i_need_a_better_name (μ : YoungDiagram) (j : ℕ) :
  Multiset.card (Multiset.filter (fun s ↦ j < s) (Multiset.map μ.rowLen (Multiset.range μ.length)))
    = Finset.card (Finset.filter (fun s ↦ j < μ.rowLen s) (Finset.range μ.length)) := by

  sorry

instance Finite_cells_ofPartition {n : ℕ} (p : Nat.Partition n) : Finite (cells_ofPartition p) := by
  apply Finite.of_injective (fun x ↦ (⟨⟨x.1.1, ?_⟩,⟨x.1.2, ?_⟩⟩ :
      (Finset.range n) × (Finset.range n)))
  · intro ⟨⟨i₁,j₁⟩, h₁⟩ ⟨⟨i₂,j₂⟩, h₂⟩
    simp
  all_goals rw [Finset.mem_range]; have := x.2; simp_rw [cells_ofPartition, Set.mem_setOf] at this
  · apply lt_of_lt_of_le this
    simp only [Set.mem_setOf_eq, gt_iff_lt]
    have : Multiset.card (Multiset.filter (fun s ↦ x.1.2 < s) p.parts) ≤ Multiset.card p.parts := by
      apply Multiset.card_le_card
      apply Multiset.filter_le
    apply le_trans this
    simp_rw [← p.parts_sum, ← Multiset.toFinset_sum_count_eq, Finset.sum_multiset_count p.parts]
    gcongr with m hm
    nth_rw 1 [← mul_one (Multiset.count _ p.parts)]
    rw [smul_eq_mul]
    apply Nat.mul_le_mul_left
    rw [Multiset.mem_toFinset] at hm
    apply p.parts_pos at hm
    exact hm
  · have : 0 < Multiset.card (Multiset.filter (fun s ↦ s > x.1.2) p.parts) := by
      apply lt_of_le_of_lt _ this
      simp
    rw [Multiset.card_pos] at this
    apply Multiset.exists_mem_of_ne_zero at this
    obtain ⟨s, hs⟩ := this
    simp only [Multiset.mem_filter, Multiset.mem_map] at hs
    obtain ⟨hsp, hsi⟩ := hs
    apply lt_of_lt_of_le hsi
    simp_rw [← p.parts_sum]
    exact Multiset.le_sum_of_mem hsp


noncomputable def ofPartition {n : ℕ} (p : Nat.Partition n) : YoungDiagram where
  cells := Set.Finite.toFinset (Finite_cells_ofPartition p)
  isLowerSet := by
    intro ⟨i₁,j₁⟩ ⟨i₂,j₂⟩ hij h
    simp only [Prod.mk_le_mk, cells_ofPartition, gt_iff_lt, Set.Finite.coe_toFinset,
      Set.mem_setOf_eq] at *
    apply lt_of_le_of_lt hij.1 (lt_of_lt_of_le h _)
    apply Multiset.card_le_card
    rw [Multiset.le_filter]
    constructor
    · exact Multiset.filter_le (fun s ↦ s > j₁) p.parts
    · intro a ha
      simp only [Multiset.mem_filter] at ha
      exact lt_of_le_of_lt hij.2 ha.2

lemma lt_rowLen_iff_lt_colLen {μ : YoungDiagram} {i j : ℕ} : j < μ.rowLen i ↔ i < μ.colLen j := by
  rw [← mem_iff_lt_colLen, ← mem_iff_lt_rowLen]

noncomputable def equivPartition : YoungDiagram ≃ Σ n : ℕ, (Nat.Partition n) where
  toFun := fun μ ↦ ⟨μ.card, μ.toPartition⟩
  invFun := fun ⟨n, p⟩ ↦ ofPartition p
  left_inv := by
    simp only
    intro μ
    ext ⟨i, j⟩
    simp only [mem_cells]
    constructor
    · intro h
      rw [ofPartition, toPartition] at h
      simp_rw [← YoungDiagram.mem_cells] at h
      simp at h
      rw [cells_ofPartition] at h
      simp at h
      rw [YoungDiagram.mem_iff_lt_rowLen] --, rowLen_eq_card]
      have (h : j < μ.rowLen 0) : j < μ.rowLen ((μ.colLen j) - 1) := by
          rw [lt_rowLen_iff_lt_colLen, colLen_eq_card]
          simp only [tsub_lt_self_iff, zero_lt_one, and_true]
          refine Nat.pos_iff_ne_zero.mpr ?_
          rw [Finset.card_ne_zero]
          rw [← mem_iff_lt_rowLen] at h
          use ⟨0, j⟩
          exact mk_mem_col_iff.mpr h
      by_cases h₀ : j < μ.rowLen 0
      · have hj0 := lt_rowLen_iff_lt_colLen.mp h₀
        apply this at h₀
        apply lt_of_lt_of_le h₀
        apply rowLen_anti
        apply (Nat.le_sub_one_iff_lt hj0).mpr
        apply lt_of_eq_of_lt' ?_ h
        rw [colLen_eq_card]
        rw [i_need_a_better_name]
        symm
        rw [Finset.card_nbij (fun ⟨i, j⟩ ↦ i)]
        · intro ⟨i', j'⟩ hij
          simp only [Finset.mem_filter, Finset.mem_range]
          have hjj' : j' = j := by
            rw [col_eq_prod] at hij
            simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hij
            exact hij.2
          rw [hjj'] at hij
          constructor
          · rw [YoungDiagram.length]
            rw [mem_col_iff, mem_iff_lt_colLen] at hij
            exact lt_of_lt_of_le hij.1 (μ.colLen_anti 0 j (Nat.zero_le j))
          · rw [← mem_iff_lt_rowLen, ← mk_mem_col_iff]
            exact hij
        · intro ⟨i', j'⟩ hij' ⟨i'' , j''⟩ hij'' h'
          simp only [Finset.mem_filter, Finset.mem_range] at h'
          simp only [h', Prod.mk.injEq, true_and]
          rw [col_eq_prod] at hij' hij''
          simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton] at hij' hij''
          rw [hij'.2, hij''.2]
        · simp only [Finset.coe_filter, Finset.mem_range]
          intro n hn
          rw [Set.mem_setOf_eq] at hn
          simp only [Set.mem_image, Finset.mem_coe, Prod.exists, exists_and_right, exists_eq_right]
          use j
          simp only [mem_col_iff, and_true]
          exact mem_iff_lt_rowLen.mpr hn.2
      · rw [not_lt] at h₀
        have : Multiset.card (Multiset.filter (fun s ↦ j < s)
            (Multiset.map μ.rowLen (Multiset.range μ.length))) = 0 := by
          rw [Multiset.card_eq_zero, Multiset.filter_eq_nil]
          intro x hx
          simp only [Multiset.mem_map, Multiset.mem_range] at hx
          obtain ⟨i, hi⟩ := hx
          rw [← hi.2, not_lt]
          exact le_trans (μ.rowLen_anti 0 i (Nat.zero_le i)) h₀
        rw [this] at h
        contradiction
    · intro h
      rw [ofPartition, toPartition]
      simp_rw [← YoungDiagram.mem_cells, cells_ofPartition]
      simp_rw [YoungDiagram.mem_iff_lt_rowLen] at h
      simp only [gt_iff_lt, Finset.range_val, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      rw [i_need_a_better_name]
      rw [lt_rowLen_iff_lt_colLen] at h
      apply lt_of_eq_of_lt' ?_ h
      rw [colLen_eq_card]
      rw [Finset.card_nbij (fun ⟨i, j⟩ ↦ i)]
      · intro ⟨i', j'⟩ hij
        simp only [Finset.mem_filter, Finset.mem_range]
        have hjj' : j' = j := by
          rw [col_eq_prod] at hij
          simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range] at hij
          exact hij.2
        rw [hjj'] at hij
        constructor
        · rw [YoungDiagram.length]
          rw [mem_col_iff, mem_iff_lt_colLen] at hij
          exact lt_of_lt_of_le hij.1 (μ.colLen_anti 0 j (Nat.zero_le j))
        · rw [← mem_iff_lt_rowLen, ← mk_mem_col_iff]
          exact hij
      · intro ⟨i', j'⟩ hij' ⟨i'' , j''⟩ hij'' h'
        simp only [Finset.mem_filter, Finset.mem_range] at h'
        simp only [h', Prod.mk.injEq, true_and]
        rw [col_eq_prod] at hij' hij''
        simp only [Finset.mem_coe, Finset.mem_product, Finset.mem_singleton] at hij' hij''
        rw [hij'.2, hij''.2]
      · simp only [Finset.coe_filter, Finset.mem_range]
        intro n hn
        rw [Set.mem_setOf_eq] at hn
        simp only [Set.mem_image, Finset.mem_coe, Prod.exists, exists_and_right, exists_eq_right]
        use j
        simp only [mem_col_iff, and_true]
        exact mem_iff_lt_rowLen.mpr hn.2

  right_inv := by
    intro ⟨n, p⟩
    simp only [Sigma.mk.inj_iff]
    constructor
    · rw [ofPartition, YoungDiagram.card]
      dsimp
      simp_rw [← p.parts_sum]
      have := (Finset.card_disjiUnion (Finset.range (YoungDiagram.ofPartition p).length)
        (YoungDiagram.ofPartition p).row (rows_disjoint (YoungDiagram.ofPartition p)))
      

      sorry
    · rw [ofPartition, toPartition]
      sorry

-- def toPartition (μ : YoungDiagram) : Nat.Partition μ.card where
--   parts := (μ.cells.val.map Prod.fst).dedup.map μ.rowLen
--   parts_pos := by
--     intro i hi
--     simp only [Multiset.mem_dedup, Multiset.mem_map, Finset.mem_val, mem_cells, Prod.exists,
--       exists_and_right, exists_eq_right] at hi
--     obtain ⟨x, ⟨y, h⟩, rfl⟩ := hi
--     simp only [rowLen, Nat.lt_find_iff, nonpos_iff_eq_zero, Decidable.not_not, forall_eq]
--     apply μ.isLowerSet _ h
--     exact Prod.mk_le_mk.mpr ⟨Nat.le_refl x, Nat.zero_le _⟩
--   parts_sum := by

--     sorry

end Partition

end YoungDiagram

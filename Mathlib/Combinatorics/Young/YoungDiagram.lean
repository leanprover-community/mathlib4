/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Data.Finset.Preimage

#align_import combinatorics.young.young_diagram from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

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
#align young_diagram YoungDiagram

namespace YoungDiagram

instance : SetLike YoungDiagram (ℕ × ℕ)
    where
  -- porting note: TODO: figure out how to do this correctly
  coe := fun y => y.cells
  coe_injective' μ ν h := by rwa [YoungDiagram.ext_iff, ← Finset.coe_inj]
                             -- 🎉 no goals

@[simp]
theorem mem_cells {μ : YoungDiagram} (c : ℕ × ℕ) : c ∈ μ.cells ↔ c ∈ μ :=
  Iff.rfl
#align young_diagram.mem_cells YoungDiagram.mem_cells

@[simp]
theorem mem_mk (c : ℕ × ℕ) (cells) (isLowerSet) :
    c ∈ YoungDiagram.mk cells isLowerSet ↔ c ∈ cells :=
  Iff.rfl
#align young_diagram.mem_mk YoungDiagram.mem_mk

instance decidableMem (μ : YoungDiagram) : DecidablePred (· ∈ μ) :=
  inferInstanceAs (DecidablePred (· ∈ μ.cells))
#align young_diagram.decidable_mem YoungDiagram.decidableMem

/-- In "English notation", a Young diagram is drawn so that (i1, j1) ≤ (i2, j2)
    means (i1, j1) is weakly up-and-left of (i2, j2). -/
theorem up_left_mem (μ : YoungDiagram) {i1 i2 j1 j2 : ℕ} (hi : i1 ≤ i2) (hj : j1 ≤ j2)
    (hcell : (i2, j2) ∈ μ) : (i1, j1) ∈ μ :=
  μ.isLowerSet (Prod.mk_le_mk.mpr ⟨hi, hj⟩) hcell
#align young_diagram.up_left_mem YoungDiagram.up_left_mem

section DistribLattice

@[simp]
theorem cells_subset_iff {μ ν : YoungDiagram} : μ.cells ⊆ ν.cells ↔ μ ≤ ν :=
  Iff.rfl
#align young_diagram.cells_subset_iff YoungDiagram.cells_subset_iff

@[simp]
theorem cells_ssubset_iff {μ ν : YoungDiagram} : μ.cells ⊂ ν.cells ↔ μ < ν :=
  Iff.rfl
#align young_diagram.cells_ssubset_iff YoungDiagram.cells_ssubset_iff

instance : Sup YoungDiagram
    where sup μ ν :=
    { cells := μ.cells ∪ ν.cells
      isLowerSet := by
        rw [Finset.coe_union]
        -- ⊢ IsLowerSet (↑μ.cells ∪ ↑ν.cells)
        exact μ.isLowerSet.union ν.isLowerSet }
        -- 🎉 no goals

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

instance : Inf YoungDiagram
    where inf μ ν :=
    { cells := μ.cells ∩ ν.cells
      isLowerSet := by
        rw [Finset.coe_inter]
        -- ⊢ IsLowerSet (↑μ.cells ∩ ↑ν.cells)
        exact μ.isLowerSet.inter ν.isLowerSet }
        -- 🎉 no goals

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
instance : OrderBot YoungDiagram where
  bot :=
    { cells := ∅
      isLowerSet := by
        intros a b _ h
        -- ⊢ b ∈ ↑∅
        simp only [Finset.coe_empty, Set.mem_empty_iff_false]
        -- ⊢ False
        simp only [Finset.coe_empty, Set.mem_empty_iff_false] at h }
        -- 🎉 no goals
  bot_le _ _ := by
    intro y
    -- ⊢ x✝ ∈ x✝¹
    simp only [mem_mk, Finset.not_mem_empty] at y
    -- 🎉 no goals

@[simp]
theorem cells_bot : (⊥ : YoungDiagram).cells = ∅ :=
  rfl
#align young_diagram.cells_bot YoungDiagram.cells_bot

-- porting note: removed `↑`, added `.cells` and changed proof
-- @[simp] -- Porting note: simp can prove this
@[norm_cast]
theorem coe_bot : (⊥ : YoungDiagram).cells = (∅ : Set (ℕ × ℕ)) := by
  refine' Set.eq_of_subset_of_subset _ _
  -- ⊢ ↑⊥.cells ⊆ ∅
  intros x h
  -- ⊢ x ∈ ∅
  simp [mem_mk, Finset.coe_empty, Set.mem_empty_iff_false] at h
  -- ⊢ ∅ ⊆ ↑⊥.cells
  simp only [cells_bot, Finset.coe_empty, Set.empty_subset]
  -- 🎉 no goals
#align young_diagram.coe_bot YoungDiagram.coe_bot

@[simp]
theorem not_mem_bot (x : ℕ × ℕ) : x ∉ (⊥ : YoungDiagram) :=
  Finset.not_mem_empty x
#align young_diagram.not_mem_bot YoungDiagram.not_mem_bot

instance : Inhabited YoungDiagram :=
  ⟨⊥⟩

instance : DistribLattice YoungDiagram :=
  Function.Injective.distribLattice YoungDiagram.cells (fun μ ν h => by rwa [YoungDiagram.ext_iff])
                                                                        -- 🎉 no goals
    (fun _ _ => rfl) fun _ _ => rfl

end DistribLattice

/-- Cardinality of a Young diagram -/
@[reducible]
protected def card (μ : YoungDiagram) : ℕ :=
  μ.cells.card
#align young_diagram.card YoungDiagram.card

section Transpose

/-- The `transpose` of a Young diagram is obtained by swapping i's with j's. -/
def transpose (μ : YoungDiagram) : YoungDiagram where
  cells := (Equiv.prodComm _ _).finsetCongr μ.cells
  isLowerSet _ _ h := by
    simp only [Finset.mem_coe, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    -- ⊢ ↑(Equiv.prodComm ℕ ℕ).symm x✝¹ ∈ μ.cells → ↑(Equiv.prodComm ℕ ℕ).symm x✝ ∈ μ …
    intro hcell
    -- ⊢ ↑(Equiv.prodComm ℕ ℕ).symm x✝ ∈ μ.cells
    apply μ.isLowerSet _ hcell
    -- ⊢ ↑(Equiv.prodComm ℕ ℕ).symm x✝ ≤ ↑(Equiv.prodComm ℕ ℕ).symm x✝¹
    simp [h]
    -- 🎉 no goals
#align young_diagram.transpose YoungDiagram.transpose

@[simp]
theorem mem_transpose {μ : YoungDiagram} {c : ℕ × ℕ} : c ∈ μ.transpose ↔ c.swap ∈ μ := by
  simp [transpose]
  -- 🎉 no goals
#align young_diagram.mem_transpose YoungDiagram.mem_transpose

@[simp]
theorem transpose_transpose (μ : YoungDiagram) : μ.transpose.transpose = μ := by
  ext x
  -- ⊢ x ∈ (transpose (transpose μ)).cells ↔ x ∈ μ.cells
  simp
  -- 🎉 no goals
#align young_diagram.transpose_transpose YoungDiagram.transpose_transpose

theorem transpose_eq_iff_eq_transpose {μ ν : YoungDiagram} : μ.transpose = ν ↔ μ = ν.transpose := by
  constructor <;>
  -- ⊢ transpose μ = ν → μ = transpose ν
    · rintro rfl
      -- ⊢ μ = transpose (transpose μ)
      -- ⊢ transpose (transpose ν) = ν
      -- 🎉 no goals
      simp
      -- 🎉 no goals
#align young_diagram.transpose_eq_iff_eq_transpose YoungDiagram.transpose_eq_iff_eq_transpose

@[simp]
theorem transpose_eq_iff {μ ν : YoungDiagram} : μ.transpose = ν.transpose ↔ μ = ν := by
  rw [transpose_eq_iff_eq_transpose]
  -- ⊢ μ = transpose (transpose ν) ↔ μ = ν
  simp
  -- 🎉 no goals
#align young_diagram.transpose_eq_iff YoungDiagram.transpose_eq_iff

-- This is effectively both directions of `transpose_le_iff` below.
protected theorem le_of_transpose_le {μ ν : YoungDiagram} (h_le : μ.transpose ≤ ν) :
    μ ≤ ν.transpose := fun c hc => by
  simp only [mem_cells, mem_transpose]
  -- ⊢ Prod.swap c ∈ ν
  apply h_le
  -- ⊢ Prod.swap c ∈ (transpose μ).cells
  simpa
  -- 🎉 no goals
#align young_diagram.le_of_transpose_le YoungDiagram.le_of_transpose_le

@[simp]
theorem transpose_le_iff {μ ν : YoungDiagram} : μ.transpose ≤ ν.transpose ↔ μ ≤ ν :=
  ⟨fun h => by
    convert YoungDiagram.le_of_transpose_le h
    -- ⊢ ν = transpose (transpose ν)
    simp, fun h => by
    -- 🎉 no goals
    rw [←transpose_transpose μ] at h
    -- ⊢ transpose μ ≤ transpose ν
    exact YoungDiagram.le_of_transpose_le h ⟩
    -- 🎉 no goals
#align young_diagram.transpose_le_iff YoungDiagram.transpose_le_iff

@[mono]
protected theorem transpose_mono {μ ν : YoungDiagram} (h_le : μ ≤ ν) : μ.transpose ≤ ν.transpose :=
  transpose_le_iff.mpr h_le
#align young_diagram.transpose_mono YoungDiagram.transpose_mono

/-- Transposing Young diagrams is an `OrderIso`. -/
@[simps]
def transposeOrderIso : YoungDiagram ≃o YoungDiagram :=
  ⟨⟨transpose, transpose, fun _ => by simp, fun _ => by simp⟩, by simp⟩
                                      -- 🎉 no goals
                                                        -- 🎉 no goals
                                                                  -- 🎉 no goals
#align young_diagram.transpose_order_iso YoungDiagram.transposeOrderIso

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
#align young_diagram.row YoungDiagram.row

theorem mem_row_iff {μ : YoungDiagram} {i : ℕ} {c : ℕ × ℕ} : c ∈ μ.row i ↔ c ∈ μ ∧ c.fst = i := by
  simp [row]
  -- 🎉 no goals
#align young_diagram.mem_row_iff YoungDiagram.mem_row_iff

theorem mk_mem_row_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.row i ↔ (i, j) ∈ μ := by simp [row]
                                                                                          -- 🎉 no goals
#align young_diagram.mk_mem_row_iff YoungDiagram.mk_mem_row_iff

protected theorem exists_not_mem_row (μ : YoungDiagram) (i : ℕ) : ∃ j, (i, j) ∉ μ := by
  obtain ⟨j, hj⟩ :=
    Infinite.exists_not_mem_finset
      (μ.cells.preimage (Prod.mk i) fun _ _ _ _ h => by
        cases h
        rfl)
  rw [Finset.mem_preimage] at hj
  -- ⊢ ∃ j, ¬(i, j) ∈ μ
  exact ⟨j, hj⟩
  -- 🎉 no goals
#align young_diagram.exists_not_mem_row YoungDiagram.exists_not_mem_row

/-- Length of a row of a Young diagram -/
def rowLen (μ : YoungDiagram) (i : ℕ) : ℕ :=
  Nat.find <| μ.exists_not_mem_row i
#align young_diagram.row_len YoungDiagram.rowLen

theorem mem_iff_lt_rowLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ j < μ.rowLen i := by
  rw [rowLen, Nat.lt_find_iff]
  -- ⊢ (i, j) ∈ μ ↔ ∀ (m : ℕ), m ≤ j → ¬¬(i, m) ∈ μ
  push_neg
  -- ⊢ (i, j) ∈ μ ↔ ∀ (m : ℕ), m ≤ j → (i, m) ∈ μ
  exact ⟨fun h _ hmj => μ.up_left_mem (by rfl) hmj h, fun h => h _ (by rfl)⟩
  -- 🎉 no goals
#align young_diagram.mem_iff_lt_row_len YoungDiagram.mem_iff_lt_rowLen

theorem row_eq_prod {μ : YoungDiagram} {i : ℕ} : μ.row i = {i} ×ˢ Finset.range (μ.rowLen i) := by
  ext ⟨a, b⟩
  -- ⊢ (a, b) ∈ row μ i ↔ (a, b) ∈ {i} ×ˢ Finset.range (rowLen μ i)
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_row_iff,
    mem_iff_lt_rowLen, and_comm, and_congr_right_iff]
  rintro rfl
  -- ⊢ b < rowLen μ a ↔ b < rowLen μ a
  rfl
  -- 🎉 no goals
#align young_diagram.row_eq_prod YoungDiagram.row_eq_prod

theorem rowLen_eq_card (μ : YoungDiagram) {i : ℕ} : μ.rowLen i = (μ.row i).card := by
  simp [row_eq_prod]
  -- 🎉 no goals
#align young_diagram.row_len_eq_card YoungDiagram.rowLen_eq_card

@[mono]
theorem rowLen_anti (μ : YoungDiagram) (i1 i2 : ℕ) (hi : i1 ≤ i2) : μ.rowLen i2 ≤ μ.rowLen i1 := by
  by_contra' h_lt
  -- ⊢ False
  rw [← lt_self_iff_false (μ.rowLen i1)]
  -- ⊢ rowLen μ i1 < rowLen μ i1
  rw [← mem_iff_lt_rowLen] at h_lt ⊢
  -- ⊢ (i1, rowLen μ i1) ∈ μ
  exact μ.up_left_mem hi (by rfl) h_lt
  -- 🎉 no goals
#align young_diagram.row_len_anti YoungDiagram.rowLen_anti

end Rows

section Columns

/-! ### Columns and column lengths of Young diagrams.

This section has an identical API to the rows section. -/


/-- The `j`-th column of a Young diagram consists of the cells whose second coordinate is `j`. -/
def col (μ : YoungDiagram) (j : ℕ) : Finset (ℕ × ℕ) :=
  μ.cells.filter fun c => c.snd = j
#align young_diagram.col YoungDiagram.col

theorem mem_col_iff {μ : YoungDiagram} {j : ℕ} {c : ℕ × ℕ} : c ∈ μ.col j ↔ c ∈ μ ∧ c.snd = j := by
  simp [col]
  -- 🎉 no goals
#align young_diagram.mem_col_iff YoungDiagram.mem_col_iff

theorem mk_mem_col_iff {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ.col j ↔ (i, j) ∈ μ := by simp [col]
                                                                                          -- 🎉 no goals
#align young_diagram.mk_mem_col_iff YoungDiagram.mk_mem_col_iff

protected theorem exists_not_mem_col (μ : YoungDiagram) (j : ℕ) : ∃ i, (i, j) ∉ μ.cells := by
  convert μ.transpose.exists_not_mem_row j using 1
  -- ⊢ (fun i => ¬(i, j) ∈ μ.cells) = fun j_1 => ¬(j, j_1) ∈ transpose μ
  simp
  -- 🎉 no goals
#align young_diagram.exists_not_mem_col YoungDiagram.exists_not_mem_col

/-- Length of a column of a Young diagram -/
def colLen (μ : YoungDiagram) (j : ℕ) : ℕ :=
  Nat.find <| μ.exists_not_mem_col j
#align young_diagram.col_len YoungDiagram.colLen

@[simp]
theorem colLen_transpose (μ : YoungDiagram) (j : ℕ) : μ.transpose.colLen j = μ.rowLen j := by
  simp [rowLen, colLen]
  -- 🎉 no goals
#align young_diagram.col_len_transpose YoungDiagram.colLen_transpose

@[simp]
theorem rowLen_transpose (μ : YoungDiagram) (i : ℕ) : μ.transpose.rowLen i = μ.colLen i := by
  simp [rowLen, colLen]
  -- 🎉 no goals
#align young_diagram.row_len_transpose YoungDiagram.rowLen_transpose

theorem mem_iff_lt_colLen {μ : YoungDiagram} {i j : ℕ} : (i, j) ∈ μ ↔ i < μ.colLen j := by
  rw [← rowLen_transpose, ← mem_iff_lt_rowLen]
  -- ⊢ (i, j) ∈ μ ↔ (j, i) ∈ transpose μ
  simp
  -- 🎉 no goals
#align young_diagram.mem_iff_lt_col_len YoungDiagram.mem_iff_lt_colLen

theorem col_eq_prod {μ : YoungDiagram} {j : ℕ} : μ.col j = Finset.range (μ.colLen j) ×ˢ {j} := by
  ext ⟨a, b⟩
  -- ⊢ (a, b) ∈ col μ j ↔ (a, b) ∈ Finset.range (colLen μ j) ×ˢ {j}
  simp only [Finset.mem_product, Finset.mem_singleton, Finset.mem_range, mem_col_iff,
    mem_iff_lt_colLen, and_comm, and_congr_right_iff]
  rintro rfl
  -- ⊢ a < colLen μ b ↔ a < colLen μ b
  rfl
  -- 🎉 no goals
#align young_diagram.col_eq_prod YoungDiagram.col_eq_prod

theorem colLen_eq_card (μ : YoungDiagram) {j : ℕ} : μ.colLen j = (μ.col j).card := by
  simp [col_eq_prod]
  -- 🎉 no goals
#align young_diagram.col_len_eq_card YoungDiagram.colLen_eq_card

@[mono]
theorem colLen_anti (μ : YoungDiagram) (j1 j2 : ℕ) (hj : j1 ≤ j2) : μ.colLen j2 ≤ μ.colLen j1 := by
  convert μ.transpose.rowLen_anti j1 j2 hj using 1 <;> simp
  -- ⊢ colLen μ j2 = rowLen (transpose μ) j2
                                                       -- 🎉 no goals
                                                       -- 🎉 no goals
#align young_diagram.col_len_anti YoungDiagram.colLen_anti

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
#align young_diagram.row_lens YoungDiagram.rowLens

-- Porting note: use `List.get` instead of `List.nthLe` because it has been deprecated
@[simp]
theorem get_rowLens {μ : YoungDiagram} {i} :
    μ.rowLens.get i = μ.rowLen i := by simp only [rowLens, List.get_range, List.get_map]
                                       -- 🎉 no goals
#align young_diagram.nth_le_row_lens YoungDiagram.get_rowLens

@[simp]
theorem length_rowLens {μ : YoungDiagram} : μ.rowLens.length = μ.colLen 0 := by
  simp only [rowLens, List.length_map, List.length_range]
  -- 🎉 no goals
#align young_diagram.length_row_lens YoungDiagram.length_rowLens

theorem rowLens_sorted (μ : YoungDiagram) : μ.rowLens.Sorted (· ≥ ·) :=
  (List.pairwise_le_range _).map _ μ.rowLen_anti
#align young_diagram.row_lens_sorted YoungDiagram.rowLens_sorted

theorem pos_of_mem_rowLens (μ : YoungDiagram) (x : ℕ) (hx : x ∈ μ.rowLens) : 0 < x := by
  rw [rowLens, List.mem_map] at hx
  -- ⊢ 0 < x
  obtain ⟨i, hi, rfl : μ.rowLen i = x⟩ := hx
  -- ⊢ 0 < rowLen μ i
  rwa [List.mem_range, ← mem_iff_lt_colLen, mem_iff_lt_rowLen] at hi
  -- 🎉 no goals
#align young_diagram.pos_of_mem_row_lens YoungDiagram.pos_of_mem_rowLens

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
#align young_diagram.cells_of_row_lens YoungDiagram.cellsOfRowLens

-- Porting note: use `List.get` instead of `List.nthLe` because it has been deprecated
protected theorem mem_cellsOfRowLens {w : List ℕ} {c : ℕ × ℕ} :
    c ∈ YoungDiagram.cellsOfRowLens w ↔ ∃ h : c.fst < w.length, c.snd < w.get ⟨c.fst, h⟩  := by
  induction' w with w_hd w_tl w_ih generalizing c <;> rw [YoungDiagram.cellsOfRowLens]
  -- ⊢ c ∈ YoungDiagram.cellsOfRowLens [] ↔ ∃ h, c.snd < List.get [] { val := c.fst …
                                                      -- ⊢ c ∈ ∅ ↔ ∃ h, c.snd < List.get [] { val := c.fst, isLt := h }
                                                      -- ⊢ c ∈ {0} ×ˢ Finset.range w_hd ∪ Finset.map (Embedding.prodMap { toFun := Nat. …
  · simp [YoungDiagram.cellsOfRowLens]
    -- 🎉 no goals
  · rcases c with ⟨⟨_, _⟩, _⟩
    -- ⊢ (Nat.zero, snd✝) ∈ {0} ×ˢ Finset.range w_hd ∪ Finset.map (Embedding.prodMap  …
    · simp
      -- 🎉 no goals
    -- Porting note: was `simpa`
    · simp [w_ih, -Finset.singleton_product, Nat.succ_lt_succ_iff]
      -- 🎉 no goals
#align young_diagram.mem_cells_of_row_lens YoungDiagram.mem_cellsOfRowLens

-- Porting note: use `List.get` instead of `List.nthLe` because it has been deprecated
/-- Young diagram from a sorted list -/
def ofRowLens (w : List ℕ) (hw : w.Sorted (· ≥ ·)) : YoungDiagram
    where
  cells := YoungDiagram.cellsOfRowLens w
  isLowerSet := by
    rintro ⟨i2, j2⟩ ⟨i1, j1⟩ ⟨hi : i1 ≤ i2, hj : j1 ≤ j2⟩ hcell
    -- ⊢ (i1, j1) ∈ ↑(YoungDiagram.cellsOfRowLens w)
    rw [Finset.mem_coe, YoungDiagram.mem_cellsOfRowLens] at hcell ⊢
    -- ⊢ ∃ h, (i1, j1).snd < List.get w { val := (i1, j1).fst, isLt := h }
    obtain ⟨h1, h2⟩ := hcell
    -- ⊢ ∃ h, (i1, j1).snd < List.get w { val := (i1, j1).fst, isLt := h }
    refine' ⟨hi.trans_lt h1, _⟩
    -- ⊢ (i1, j1).snd < List.get w { val := (i1, j1).fst, isLt := (_ : i1 < List.leng …
    calc
      j1 ≤ j2 := hj
      _ < w.get ⟨i2, _⟩  := h2
      _ ≤ w.get ⟨i1, _⟩ := by
        obtain rfl | h := eq_or_lt_of_le hi
        · convert le_refl (w.get ⟨i1, h1⟩)
        · exact List.pairwise_iff_get.mp hw _ _ h
#align young_diagram.of_row_lens YoungDiagram.ofRowLens

-- Porting note: use `List.get` instead of `List.nthLe` because it has been deprecated
theorem mem_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} {c : ℕ × ℕ} :
    c ∈ ofRowLens w hw ↔ ∃ h : c.fst < w.length, c.snd < w.get ⟨c.fst, h⟩ :=
  YoungDiagram.mem_cellsOfRowLens
#align young_diagram.mem_of_row_lens YoungDiagram.mem_ofRowLens

/-- The number of rows in `ofRowLens w hw` is the length of `w` -/
theorem rowLens_length_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens.length = w.length := by
  simp only [length_rowLens, colLen, Nat.find_eq_iff, mem_cells, mem_ofRowLens,
    lt_self_iff_false, IsEmpty.exists_iff, Classical.not_not]
  refine' ⟨True.intro, fun n hn => ⟨hn, hpos _ (List.get_mem _ _ hn)⟩⟩
  -- 🎉 no goals
#align young_diagram.row_lens_length_of_row_lens YoungDiagram.rowLens_length_ofRowLens

-- Porting note: use `List.get` instead of `List.nthLe` because it has been deprecated
/-- The length of the `i`th row in `ofRowLens w hw` is the `i`th entry of `w` -/
theorem rowLen_ofRowLens {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (i : Fin w.length) :
    (ofRowLens w hw).rowLen i = w.get i := by
  simp [rowLen, Nat.find_eq_iff, mem_ofRowLens]
  -- 🎉 no goals
#align young_diagram.row_len_of_row_lens YoungDiagram.rowLen_ofRowLens

/-- The left_inv direction of the equivalence -/
theorem ofRowLens_to_rowLens_eq_self {μ : YoungDiagram} : ofRowLens _ (rowLens_sorted μ) = μ := by
  ext ⟨i, j⟩
  -- ⊢ (i, j) ∈ (ofRowLens (rowLens μ) (_ : List.Sorted (fun x x_1 => x ≥ x_1) (row …
  simp only [mem_cells, mem_ofRowLens, length_rowLens, get_rowLens]
  -- ⊢ (∃ h, j < rowLen μ i) ↔ (i, j) ∈ μ
  simpa [← mem_iff_lt_colLen, mem_iff_lt_rowLen] using j.zero_le.trans_lt
  -- 🎉 no goals
#align young_diagram.of_row_lens_to_row_lens_eq_self YoungDiagram.ofRowLens_to_rowLens_eq_self

/-- The right_inv direction of the equivalence -/
theorem rowLens_ofRowLens_eq_self {w : List ℕ} {hw : w.Sorted (· ≥ ·)} (hpos : ∀ x ∈ w, 0 < x) :
    (ofRowLens w hw).rowLens = w :=
  -- Porting note: golf by `List.get`
  List.ext_get (rowLens_length_ofRowLens hpos) fun i _ h₂ =>
    get_rowLens.trans <| rowLen_ofRowLens ⟨i, h₂⟩
#align young_diagram.row_lens_of_row_lens_eq_self YoungDiagram.rowLens_ofRowLens_eq_self

/-- Equivalence between Young diagrams and weakly decreasing lists of positive natural numbers.
A Young diagram `μ` is equivalent to a list of row lengths. -/
@[simps]
def equivListRowLens : YoungDiagram ≃ { w : List ℕ // w.Sorted (· ≥ ·) ∧ ∀ x ∈ w, 0 < x }
    where
  toFun μ := ⟨μ.rowLens, μ.rowLens_sorted, μ.pos_of_mem_rowLens⟩
  invFun ww := ofRowLens ww.1 ww.2.1
  left_inv _ := ofRowLens_to_rowLens_eq_self
  right_inv := fun ⟨_, hw⟩ => Subtype.mk_eq_mk.mpr (rowLens_ofRowLens_eq_self hw.2)
#align young_diagram.equiv_list_row_lens YoungDiagram.equivListRowLens

end EquivListRowLens

end YoungDiagram

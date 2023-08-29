/-
Copyright (c) 2022 Jake Levinson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jake Levinson
-/
import Mathlib.Combinatorics.Young.YoungDiagram

#align_import combinatorics.young.semistandard_tableau from "leanprover-community/mathlib"@"b363547b3113d350d053abdf2884e9850a56b205"

/-!
# Semistandard Young tableaux

A semistandard Young tableau is a filling of a Young diagram by natural numbers, such that
the entries are weakly increasing left-to-right along rows (i.e. for fixed `i`), and
strictly-increasing top-to-bottom along columns (i.e. for fixed `j`).

An example of an SSYT of shape `μ = [4, 2, 1]` is:

```text
0 0 0 2
1 1
2
```

We represent an SSYT as a function `ℕ → ℕ → ℕ`, which is required to be zero for all pairs
`(i, j) ∉ μ` and to satisfy the row-weak and column-strict conditions on `μ`.


## Main definitions

- `Ssyt (μ : YoungDiagram)`: semistandard Young tableaux of shape `μ`. There is
  a `coe` instance such that `T i j` is value of the `(i, j)` entry of the SSYT `T`.
- `Ssyt.highestWeight (μ : YoungDiagram)`: the semistandard Young tableau whose `i`th row
  consists entirely of `i`s, for each `i`.

## Tags

Semistandard Young tableau

## References

<https://en.wikipedia.org/wiki/Young_tableau>

-/


/-- A semistandard Young tableau (SSYT) is a filling of the cells of a Young diagram by natural
numbers, such that the entries in each row are weakly increasing (left to right), and the entries
in each column are strictly increasing (top to bottom).

Here, an SSYT is represented as an unrestricted function `ℕ → ℕ → ℕ` that, for reasons
of extensionality, is required to vanish outside `μ`. -/
structure Ssyt (μ : YoungDiagram) where
  /-- `entry i j` is value of the `(i, j)` entry of the SSYT `μ`. -/
  entry : ℕ → ℕ → ℕ
  /-- The entries in each row are weakly increasing (left to right). -/
  row_weak' : ∀ {i j1 j2 : ℕ}, j1 < j2 → (i, j2) ∈ μ → entry i j1 ≤ entry i j2
  /-- The entries in each column are strictly increasing (top to bottom). -/
  col_strict' : ∀ {i1 i2 j : ℕ}, i1 < i2 → (i2, j) ∈ μ → entry i1 j < entry i2 j
  /-- `entry` is required to be zero for all pairs `(i, j) ∉ μ`. -/
  zeros' : ∀ {i j}, (i, j) ∉ μ → entry i j = 0
#align ssyt Ssyt

namespace Ssyt

instance funLike {μ : YoungDiagram} : FunLike (Ssyt μ) ℕ fun _ ↦ ℕ → ℕ where
  coe := Ssyt.entry
  coe_injective' T T' h := by
    cases T
    -- ⊢ { entry := entry✝, row_weak' := row_weak'✝, col_strict' := col_strict'✝, zer …
    cases T'
    -- ⊢ { entry := entry✝¹, row_weak' := row_weak'✝¹, col_strict' := col_strict'✝¹,  …
    congr
    -- 🎉 no goals
#align ssyt.fun_like Ssyt.funLike

/-- Helper instance for when there's too many metavariables to apply `CoeFun.coe` directly. -/
instance {μ : YoungDiagram} : CoeFun (Ssyt μ) fun _ ↦ ℕ → ℕ → ℕ :=
  inferInstance

@[simp]
theorem to_fun_eq_coe {μ : YoungDiagram} {T : Ssyt μ} : T.entry = (T : ℕ → ℕ → ℕ) :=
  rfl
#align ssyt.to_fun_eq_coe Ssyt.to_fun_eq_coe

@[ext]
theorem ext {μ : YoungDiagram} {T T' : Ssyt μ} (h : ∀ i j, T i j = T' i j) : T = T' :=
  FunLike.ext T T' fun _ ↦ by
    funext
    -- ⊢ ↑T x✝¹ x✝ = ↑T' x✝¹ x✝
    apply h
    -- 🎉 no goals
#align ssyt.ext Ssyt.ext

/-- Copy of an `Ssyt μ` with a new `entry` equal to the old one. Useful to fix definitional
equalities. -/
protected def copy {μ : YoungDiagram} (T : Ssyt μ) (entry' : ℕ → ℕ → ℕ) (h : entry' = T) : Ssyt μ
    where
  entry := entry'
  row_weak' := h.symm ▸ T.row_weak'
  col_strict' := h.symm ▸ T.col_strict'
  zeros' := h.symm ▸ T.zeros'
#align ssyt.copy Ssyt.copy

@[simp]
theorem coe_copy {μ : YoungDiagram} (T : Ssyt μ) (entry' : ℕ → ℕ → ℕ) (h : entry' = T) :
    ⇑(T.copy entry' h) = entry' :=
  rfl
#align ssyt.coe_copy Ssyt.coe_copy

theorem copy_eq {μ : YoungDiagram} (T : Ssyt μ) (entry' : ℕ → ℕ → ℕ) (h : entry' = T) :
    T.copy entry' h = T :=
  FunLike.ext' h
#align ssyt.copy_eq Ssyt.copy_eq

theorem row_weak {μ : YoungDiagram} (T : Ssyt μ) {i j1 j2 : ℕ} (hj : j1 < j2)
    (hcell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 :=
  T.row_weak' hj hcell
#align ssyt.row_weak Ssyt.row_weak

theorem col_strict {μ : YoungDiagram} (T : Ssyt μ) {i1 i2 j : ℕ} (hi : i1 < i2)
    (hcell : (i2, j) ∈ μ) : T i1 j < T i2 j :=
  T.col_strict' hi hcell
#align ssyt.col_strict Ssyt.col_strict

theorem zeros {μ : YoungDiagram} (T : Ssyt μ) {i j : ℕ} (not_cell : (i, j) ∉ μ) : T i j = 0 :=
  T.zeros' not_cell
#align ssyt.zeros Ssyt.zeros

theorem row_weak_of_le {μ : YoungDiagram} (T : Ssyt μ) {i j1 j2 : ℕ} (hj : j1 ≤ j2)
    (cell : (i, j2) ∈ μ) : T i j1 ≤ T i j2 := by
  cases' eq_or_lt_of_le hj with h h
  -- ⊢ ↑T i j1 ≤ ↑T i j2
  · rw [h]
    -- 🎉 no goals
  · exact T.row_weak h cell
    -- 🎉 no goals
#align ssyt.row_weak_of_le Ssyt.row_weak_of_le

theorem col_weak {μ : YoungDiagram} (T : Ssyt μ) {i1 i2 j : ℕ} (hi : i1 ≤ i2) (cell : (i2, j) ∈ μ) :
    T i1 j ≤ T i2 j := by
  cases' eq_or_lt_of_le hi with h h
  -- ⊢ ↑T i1 j ≤ ↑T i2 j
  · rw [h]
    -- 🎉 no goals
  · exact le_of_lt (T.col_strict h cell)
    -- 🎉 no goals
#align ssyt.col_weak Ssyt.col_weak

/-- The "highest weight" SSYT of a given shape has all i's in row i, for each i. -/
def highestWeight (μ : YoungDiagram) : Ssyt μ where
  entry i j := if (i, j) ∈ μ then i else 0
  row_weak' hj hcell := by
    simp only
    -- ⊢ (if (i✝, j1✝) ∈ μ then i✝ else 0) ≤ if (i✝, j2✝) ∈ μ then i✝ else 0
    rw [if_pos hcell, if_pos (μ.up_left_mem (by rfl) (le_of_lt hj) hcell)]
    -- 🎉 no goals
  col_strict' hi hcell := by
    simp only
    -- ⊢ (if (i1✝, j✝) ∈ μ then i1✝ else 0) < if (i2✝, j✝) ∈ μ then i2✝ else 0
    rwa [if_pos hcell, if_pos (μ.up_left_mem (le_of_lt hi) (by rfl) hcell)]
    -- 🎉 no goals
  zeros' not_cell := if_neg not_cell
#align ssyt.highest_weight Ssyt.highestWeight

@[simp]
theorem highestWeight_apply {μ : YoungDiagram} {i j : ℕ} :
    highestWeight μ i j = if (i, j) ∈ μ then i else 0 :=
  rfl
#align ssyt.highest_weight_apply Ssyt.highestWeight_apply

instance {μ : YoungDiagram} : Inhabited (Ssyt μ) :=
  ⟨Ssyt.highestWeight μ⟩

end Ssyt

/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.Order.WithBot


/-!
# Row echelon forms

This file defines the row echelon form of matrices and the leading entries of their rows.

## Main definitions

- `Matrix.IsRowEchelon` expresses that `M` is in row echelon form: an entry of a lower row
  vanishes whenever a higher row is zero at every column strictly to its left.
- `Matrix.IsLeadingEntry`: `c : WithTop n` is the leading position of row `i` of `M`,
  with `⊤` for a zero row.

## Tags

matrix, echelon form

-/

@[expose] public section

universe v

variable {m n : Type*}
variable {R : Type v} {M : Matrix m n R}

namespace Matrix

variable [Zero R]

/-- `M` is in row echelon form: for rows `i₁ < i₂`, if the higher row `i₁` is zero at every
column strictly left of `j₂`, then the lower row `i₂` is zero at `j₂`. -/
def IsRowEchelon [LT m] [LT n] (M : Matrix m n R) : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ < i₂ → ∀ ⦃j₂⦄, (∀ j₁ < j₂, M i₁ j₁ = 0) → M i₂ j₂ = 0

/-- In an echelon matrix, rows below a zero row are zero. -/
theorem IsRowEchelon.row_eq_zero_of_lt [LT m] [LT n] {i₁ i₂ : m} (he : M.IsRowEchelon)
    (hlt : i₁ < i₂) (h0 : M i₁ = 0) : M i₂ = 0 := by
  funext j
  exact he hlt fun j₁ _ => congrFun h0 j₁

/-! ### Leading entries -/

/-- `c` is the leading position of row `i`: entries strictly left of `c` vanish and, when
`c` is a column, the entry at `c` is nonzero. `c = ⊤` states that the row is zero. -/
def IsLeadingEntry [LT n] (M : Matrix m n R) (i : m) (c : WithTop n) : Prop :=
  (∀ j : n, (j : WithTop n) < c → M i j = 0) ∧ ∀ c₀ : n, c = c₀ → M i c₀ ≠ 0

@[simp]
theorem isLeadingEntry_top_iff [LT n] {i : m} :
    M.IsLeadingEntry i ⊤ ↔ M i = 0 := by
  simp [IsLeadingEntry, funext_iff]

@[simp]
theorem isLeadingEntry_coe_iff [LT n] {i : m} {c : n} :
    M.IsLeadingEntry i c ↔ (∀ j < c, M i j = 0) ∧ M i c ≠ 0 := by
  simp [IsLeadingEntry]

/-- A row has at most one leading position. -/
theorem IsLeadingEntry.unique [LinearOrder n] {i : m} {c₁ c₂ : WithTop n}
    (h₁ : M.IsLeadingEntry i c₁) (h₂ : M.IsLeadingEntry i c₂) :
    c₁ = c₂ := by
  refine le_antisymm (not_lt.mp ?_) (not_lt.mp ?_)
  · intro hlt
    obtain ⟨c₀, hc, hlt'⟩ := WithTop.lt_iff_exists_coe.mp hlt
    exact h₂.2 c₀ hc (h₁.1 c₀ hlt')
  · intro hlt
    obtain ⟨c₀, hc, hlt'⟩ := WithTop.lt_iff_exists_coe.mp hlt
    exact h₁.2 c₀ hc (h₂.1 c₀ hlt')

end Matrix

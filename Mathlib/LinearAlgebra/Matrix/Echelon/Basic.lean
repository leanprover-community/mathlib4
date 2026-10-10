/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia, Joseph Qian, Junye Ji
-/
module

public import Mathlib.Data.Fintype.Defs
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

import Mathlib.Order.WellFounded


/-!
# Row echelon forms

This file defines the row echelon form of matrices and the leading entries of their rows.

## Main definitions

- `Matrix.IsRowEchelon` expresses that `A` is in row echelon form: an entry of a lower row
  vanishes whenever a higher row is zero at every column strictly to its left.
- `Matrix.IsLeadingEntry`: `c : n` is the leading position of row `i` of `A`.
- `Matrix.IsReducedRowEchelon` additionally requires each leading entry to be `1` and the
  entries above it to vanish.
- `Matrix.IsRowEchelonOf A B` expresses that `A` is a row echelon form representation of `B`.
- `Matrix.IsReducedRowEchelonOf A B` expresses that `A` is the reduced row echelon form of `B`.

## Tags

matrix, echelon form

-/

@[expose] public section

universe v

variable {m n : Type*}
variable {R : Type v} {A : Matrix m n R}

namespace Matrix

variable [Zero R]

/-- `A` is in row echelon form: for rows `i₁ < i₂`, if the higher row `i₁` is zero at every
column strictly left of `j₂`, then the lower row `i₂` is zero at `j₂`. -/
def IsRowEchelon [LT m] [LT n] (A : Matrix m n R) : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ < i₂ → ∀ ⦃j₂⦄, (∀ j₁ < j₂, A i₁ j₁ = 0) → A i₂ j₂ = 0

/-- In an echelon matrix, rows below a zero row are zero. -/
theorem IsRowEchelon.row_eq_zero_of_lt [LT m] [LT n] {i₁ i₂ : m} (he : A.IsRowEchelon)
    (hlt : i₁ < i₂) (h0 : A i₁ = 0) : A i₂ = 0 := by
  funext j
  exact he hlt fun j₁ _ => congr($h0 j₁)

/-! ### Leading entries -/

/-- `c` is the leading position of row `i`. -/
def IsLeadingEntry [LT n] (A : Matrix m n R) (i : m) (c : n) : Prop :=
  (∀ j < c, A i j = 0) ∧ A i c ≠ 0

theorem IsLeadingEntry.row_ne_zero [LT n] {i : m} {c : n} (hc : A.IsLeadingEntry i c) :
    A i ≠ 0 :=
  fun contra => hc.2 congr($contra c)

theorem row_ne_zero_iff_exists_isLeadingEntry [LT n] [WellFoundedLT n] {i : m} :
    A i ≠ 0 ↔ ∃ c, A.IsLeadingEntry i c := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => hc.row_ne_zero⟩
  obtain ⟨c, hc, hmin⟩ := wellFounded_lt.has_min {j | A i j ≠ 0} <| Function.ne_iff.mp h
  refine ⟨c, ?_, hc⟩
  by_contra
  aesop

/-- If column indices have a linear order, then there's at most one leading position per row. -/
theorem IsLeadingEntry.unique [LinearOrder n] {i : m} {c₁ c₂ : n}
    (h₁ : A.IsLeadingEntry i c₁) (h₂ : A.IsLeadingEntry i c₂) : c₁ = c₂ :=
  le_antisymm (not_lt.mp fun hlt => h₂.2 (h₁.1 c₂ hlt)) (not_lt.mp fun hlt => h₁.2 (h₂.1 c₁ hlt))

instance [DecidableEq R] [Fintype n] [LT n] [DecidableLT n]
    (A : Matrix m n R) (i : m) (c : n) : Decidable (A.IsLeadingEntry i c) :=
  decidable_of_iff ((∀ j < c, A i j = 0) ∧ A i c ≠ 0) Iff.rfl

theorem row_eq_zero_or_exists_isLeadingEntry [LT n] [WellFoundedLT n] (i : m) :
        A i = 0 ∨ ∃ c, A.IsLeadingEntry i c := by
      by_cases hZero : A i = 0
      · exact Or.inl hZero
      · exact Or.inr (row_ne_zero_iff_exists_isLeadingEntry.mp hZero)

theorem IsRowEchelon.pivotCol_strictly_increasing [LT m] [LinearOrder n] {i j : m} {p q : n}
    (hA : A.IsRowEchelon) (hrow : i < j) (hi : A.IsLeadingEntry i p) (hj : A.IsLeadingEntry j q) :
    p < q := by
  by_contra h
  have hqp : q ≤ p := not_lt.mp h
  have h0 : ∀ j₁ < q, A i j₁ = 0 := fun j₁ hj₁ => hi.1 j₁ (lt_of_lt_of_le hj₁ hqp)
  exact hj.2 (hA hrow h0)

theorem not_isLeadingEntry_of_row_eq_zero [LT n] {i : m} {c : n}
    (h0 : A i = 0) : ¬ A.IsLeadingEntry i c := by
  intro hc
  exact hc.row_ne_zero h0

/-! ### Reduced row echelon form -/

/-- `A` is in reduced row echelon form: it is in row echelon form, each leading entry is
`1`, and entries above a leading entry vanish (entries below one vanish by
`isRowEchelon`). -/
structure IsReducedRowEchelon [LT m] [LT n] [One R] (A : Matrix m n R) : Prop where
  isRowEchelon : A.IsRowEchelon
  eq_one ⦃i : m⦄ ⦃c : n⦄ (hA : A.IsLeadingEntry i c) : A i c = 1
  eq_zero ⦃i₁ i₂ : m⦄ ⦃c : n⦄ (hlt : i₁ < i₂) (hA : A.IsLeadingEntry i₂ c) : A i₁ c = 0

/-- If the row indices have a linear order, then every entry in a pivot column vanishes
except for the pivot. -/
theorem IsReducedRowEchelon.eq_zero_of_ne_of_isLeadingEntry [LinearOrder m] [LT n] [One R]
    {i₁ i₂ : m} {c : n} (hA : A.IsReducedRowEchelon) (hne : i₁ ≠ i₂)
    (hlead : A.IsLeadingEntry i₂ c) : A i₁ c = 0 := by
  rcases hne.lt_or_gt with hlt | hlt
  · exact hA.eq_zero hlt hlead
  · exact hA.isRowEchelon hlt hlead.1

variable [CommRing R] [DecidableEq m] [Fintype m]

/-- `A` is a row-echelon-form representative of `B`. -/
structure IsRowEchelonOf [LT m] [LT n] (A B : Matrix m n R) : Prop where
  rowEquivalent : RowEquivalent A B
  isRowEchelon : IsRowEchelon A

/-- `A` is a reduced-row-echelon-form representative of `B`. -/
structure IsReducedRowEchelonOf [LT m] [LT n] (A B : Matrix m n R) : Prop where
  rowEquivalent : RowEquivalent A B
  isReducedRowEchelon : IsReducedRowEchelon A

/-- A reduced-echelon representative is also an echelon representative. -/
theorem IsReducedRowEchelonOf.isRowEchelon [LT m] [LT n] {A B : Matrix m n R}
    (h : IsReducedRowEchelonOf A B) : IsRowEchelonOf A B :=
  ⟨h.rowEquivalent, h.isReducedRowEchelon.isRowEchelon⟩

end Matrix

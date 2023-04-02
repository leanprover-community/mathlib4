/-
Copyright (c) 2021 Lu-Ming Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lu-Ming Zhang

! This file was ported from Lean 3 source module linear_algebra.matrix.orthogonal
! leanprover-community/mathlib commit 790e98fbb5ec433d89d833320954607e79ae9071
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Matrix.Basic

/-!
# Orthogonal

This file contains definitions and properties concerning orthogonality of rows and columns.

## Main results

- `Matrix.OrthogonalRows`:
  `A.OrthogonalRows` means `A` has orthogonal (with respect to `dotProduct`) rows.
- `Matrix.OrthogonalCols`:
  `A.OrthogonalCols` means `A` has orthogonal (with respect to `dotProduct`) columns.

## Tags

orthogonal
-/


namespace Matrix

variable {α n m : Type _}

variable [Mul α] [AddCommMonoid α]

variable (A : Matrix m n α)

open Matrix

/-- `A.OrthogonalRows` means matrix `A` has orthogonal rows (with respect to
`Matrix.dotProduct`). -/
def OrthogonalRows [Fintype n] : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ ≠ i₂ → dotProduct (A i₁) (A i₂) = 0
#align matrix.has_orthogonal_rows Matrix.OrthogonalRows

/-- `A.OrthogonalCols` means matrix `A` has orthogonal columns (with respect to
`Matrix.dotProduct`). -/
def OrthogonalCols [Fintype m] : Prop :=
  OrthogonalRows Aᵀ
#align matrix.has_orthogonal_cols Matrix.OrthogonalCols

/-- `Aᵀ` has orthogonal rows iff `A` has orthogonal columns. -/
@[simp]
theorem transpose_OrthogonalRows_iff_OrthogonalCols [Fintype m] :
    Aᵀ.OrthogonalRows ↔ A.OrthogonalCols :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_rows_iff_has_orthogonal_cols Matrix.transpose_OrthogonalRows_iff_OrthogonalCols

/-- `Aᵀ` has orthogonal columns iff `A` has orthogonal rows. -/
@[simp]
theorem transpose_OrthogonalCols_iff_OrthogonalRows [Fintype n] :
    Aᵀ.OrthogonalCols ↔ A.OrthogonalRows :=
  Iff.rfl
#align matrix.transpose_has_orthogonal_cols_iff_has_orthogonal_rows Matrix.transpose_OrthogonalCols_iff_OrthogonalRows

variable {A}

theorem OrthogonalRows.OrthogonalCols [Fintype m] (h : Aᵀ.OrthogonalRows) :
    A.OrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.has_orthogonal_cols Matrix.OrthogonalRows.OrthogonalCols

theorem OrthogonalCols.transpose_OrthogonalRows [Fintype m] (h : A.OrthogonalCols) :
    Aᵀ.OrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.transpose_has_orthogonal_rows Matrix.OrthogonalCols.transpose_OrthogonalRows

theorem OrthogonalCols.OrthogonalRows [Fintype n] (h : Aᵀ.OrthogonalCols) :
    A.OrthogonalRows :=
  h
#align matrix.has_orthogonal_cols.has_orthogonal_rows Matrix.OrthogonalCols.OrthogonalRows

theorem OrthogonalRows.transpose_OrthogonalCols [Fintype n] (h : A.OrthogonalRows) :
    Aᵀ.OrthogonalCols :=
  h
#align matrix.has_orthogonal_rows.transpose_has_orthogonal_cols Matrix.OrthogonalRows.transpose_OrthogonalCols

end Matrix

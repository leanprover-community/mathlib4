/-
Copyright (c) 2026 Rao Xiaojia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rao Xiaojia
-/
module

public import Mathlib.LinearAlgebra.Matrix.Defs


/-!
# Row echelon forms

This file defines the row echelon form of matrices.

## Main definitions

- `Matrix.RowEchelon` expresses that `M` is in row echelon form: an entry of a lower row
  vanishes whenever a higher row is zero at every column strictly to its left.

## Tags

matrix, echelon form

-/

@[expose] public section

universe v

variable {m n : Type*}
variable {R : Type v} {M : Matrix m n R}

namespace Matrix

section LT

variable [LT m] [LT n]

section Zero

variable [Zero R]

/-- `M` is in row echelon form: for rows `i₁ < i₂`, if the higher row `i₁` is zero at every
column strictly left of `j₂`, then the lower row `i₂` is zero at `j₂`. -/
def RowEchelon (M : Matrix m n R) : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ < i₂ → ∀ ⦃j₂⦄, (∀ j₁ < j₂, M i₁ j₁ = 0) → M i₂ j₂ = 0

end Zero

end LT

end Matrix

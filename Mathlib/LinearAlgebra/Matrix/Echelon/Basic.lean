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

- `Matrix.RowEchelon` expresses that `M` is in row echelon form: every
  nonzero entry of a lower row is preceded, in any higher row, by a nonzero entry
  strictly to its left.

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

/-- `M` is in row echelon form: for any rows `i₁ < i₂`, every nonzero entry of the
lower row `i₂` lies strictly to the right of some nonzero entry of the upper row `i₁`. -/
def RowEchelon (M : Matrix m n R) : Prop :=
  ∀ ⦃i₁ i₂⦄, i₁ < i₂ → ∀ ⦃j₂⦄, M i₂ j₂ ≠ 0 → ∃ j₁ < j₂, M i₁ j₁ ≠ 0

end Zero

end LT

end Matrix

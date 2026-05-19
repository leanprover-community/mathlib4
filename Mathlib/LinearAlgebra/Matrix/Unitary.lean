/-
Copyright (c) 2026 Scott Wesley. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Wesley
-/
module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.UnitaryGroup

public import Mathlib.Data.Complex.Basic

/-!
# Hermitian unitary matrices

In this file we prove that Hermitian unitary matrices are self-inverse.
-/

public section

namespace Matrix

universe u v

variable {n : Type u} [DecidableEq n] [Fintype n]
variable {α : Type v} [CommRing α] [StarRing α]
variable {M : Matrix n n α}

/-- If `M` is both Hermitian and unitary, then it squares to the identity mactrix. -/
theorem involution_of_hermitian_of_unitary (h₁ : M.IsHermitian) (h₂ : M ∈ Matrix.unitaryGroup n α) :
    M * M = 1 := by
  nth_rw 2 [←h₁]
  rw [←Matrix.star_eq_conjTranspose]
  rw [Matrix.mem_unitaryGroup_iff.mp h₂]

end Matrix

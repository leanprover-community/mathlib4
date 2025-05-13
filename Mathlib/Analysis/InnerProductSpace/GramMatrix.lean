/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/

import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semi-definiteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.Gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → α` for an
`InnerProductSpace 𝕜 α`.

## Main results

* `Matrix.IsGram.PosSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix

open scoped InnerProductSpace

open scoped ComplexOrder

variable {E n : Type*}
variable {α : Type*}
variable {𝕜 : Type*} [RCLike 𝕜]
variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def gram (𝕜 : Type*) [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    (v : n → E) : Matrix n n 𝕜 := fun i j ↦ inner 𝕜 (v i) (v j)

local notation "⟪" x ", " y "⟫" => @inner 𝕜  _ _ x y

/-- A `M : Matrix n n 𝕜` is a Gram matrix if `M = Gram 𝕜 v` for some `v : n → E`. -/
def IsGram (M : Matrix n n 𝕜) : Prop := ∃ (v : n → E), (M = gram 𝕜 v)

namespace IsGram

/-- For the matrix `gram 𝕜 v`, the entry at `i j : n` equals `⟪v i, v j⟫`. -/
lemma entry {v : n → E} (i j : n) : (gram _ v) i j = ⟪v i, v j⟫ := by
  rw [gram]

/-- A Gram matrix is Hermitian. -/
lemma IsHermitian {v : n → E} : (gram 𝕜 v).IsHermitian := by
  refine IsHermitian.ext_iff.mpr (fun i j ↦ ?_)
  rw [gram, gram]
  simp only [RCLike.star_def, inner_conj_symm]

/-- A Gram matrix is positive semidefinite. -/
theorem PosSemidef [Fintype n] {v : n → E} :
    PosSemidef (gram 𝕜 v) := by
  refine ⟨IsHermitian, fun x ↦ ?_⟩
  let y := ∑ (i : n), x i • v i
  have h : ⟪y, y⟫ = star x ⬝ᵥ (gram 𝕜 v) *ᵥ x := by
    simp [y]
    calc
      ⟪y, y⟫ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ⟪v i, v j⟫) := by
          simp_rw [y, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
        _ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ((gram 𝕜 v) i j)) := by
          simp_rw [entry]
        _ = star x ⬝ᵥ (gram 𝕜 v) *ᵥ x := by
          simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct,
            mul_comm, ← star_def]
          rfl
  rw [← h, le_iff_re_im]
  refine ⟨?_, ?_⟩
  · simp only [map_zero]
    exact inner_self_nonneg
  · simp only [map_zero, inner_self_im, y]

end IsGram

end Matrix

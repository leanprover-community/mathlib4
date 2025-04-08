/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Peter Pfaffelhuber
-/
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semi-definiteness.
Results require `𝕜 = ℝ` or `ℂ`.

## Main definition

* `Matrix.Gram` : a matrix `M : Matrix n n 𝕜` is a Gram matrix if
`M i j = ⟪v i, v j⟫` for all `i j : n`, where
`v : n → E` for an `InnerProductSpace E`.

## Main results

* `Matrix.Gram.PosSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix Topology ComplexConjugate Finsupp

open LinearMap (BilinForm)

variable {𝕜 E F n : Type*} [RCLike 𝕜]

section BasicProperties_Seminormed

open scoped InnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def Gram (M : Matrix n n 𝕜) (v : n → E) : Prop := ∀ i j, M i j = ⟪v i, v j⟫

namespace Gram

lemma IsHermitian (M : Matrix n n 𝕜) {v : n → E} (hM : Gram M v) : M.IsHermitian := by
  refine IsHermitian.ext_iff.mpr ?_
  intro i j
  rw [hM, hM]
  simp only [RCLike.star_def, inner_conj_symm]

variable [Fintype n]

variable [PartialOrder 𝕜]

theorem PosDef (M : Matrix n n 𝕜) {v : n → E} (hM : M.Gram v) : PosSemidef M := by
  simp [PosSemidef]
  refine ⟨Gram.IsHermitian M hM, ?_⟩
  intro x
  --  let y : E := ∑ (i : n), (x i) • (v i)

  rw [nonneg_iff]

  refine nonneg_iff.mpr ?_


  apply?

/-

  refine nonneg_iff.mpr ⟨?_, ?_⟩

  · calc
      0 ≤ re (inner y y) := by
        exact inner_self_nonneg
      _ = RCLike.re (∑ (i : n), ∑ (j : n), (x i) * (x j) * (inner (v i) (v j))) := by sorry
      _ = RCLike.re (∑ (i : n), ∑ (j : n), (x i) * (x j) * (M i j)) := by sorry
      _ = RCLike.re (star x ⬝ᵥ M *ᵥ x) := by sorry
    · sorry inner_self_im
-/

end Gram

end Matrix

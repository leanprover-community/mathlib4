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

* `Matrix.gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → E` for an
  `Inner 𝕜 E`.

## Main results

* `Matrix.gram_posSemidef` Gram matrices are positive semi-definite.
-/

open RCLike Real Matrix

open scoped InnerProductSpace

open scoped ComplexOrder

variable {E n : Type*}
variable {α : Type*}
variable {𝕜 : Type*}
namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n → E) : Matrix n n 𝕜 := of fun i j ↦ inner 𝕜 (v i) (v j)

local notation "⟪" x ", " y "⟫" => @inner 𝕜  _ _ x y

/-- For the matrix `gram 𝕜 v`, the entry at `i j : n` equals `⟪v i, v j⟫`. -/
lemma gram_apply [Inner 𝕜 E] {v : n → E} (i j : n) :
    (gram _ v) i j = ⟪v i, v j⟫ := by
  rw [gram, of_apply]

/-- A Gram matrix is Hermitian. -/
lemma isHermitian_gram [RCLike 𝕜]
[SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {v : n → E} : (gram 𝕜 v).IsHermitian := by
  refine IsHermitian.ext_iff.mpr (fun i j ↦ ?_)
  rw [gram, of_apply, of_apply]
  simp only [RCLike.star_def, inner_conj_symm]

theorem gram_eq [RCLike 𝕜]
[SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]
 [Fintype n] {v : n → E} (y : E) (x : n → 𝕜) (hy : y = ∑ i, x i • v i) :
    ⟪y, y⟫ = star x ⬝ᵥ (gram 𝕜 v) *ᵥ x := by
  calc
  ⟪y, y⟫ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ⟪v i, v j⟫) := by
    simp_rw [hy, sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
  _ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ((gram 𝕜 v) i j)) := by
    simp_rw [gram_apply]
  _ = star x ⬝ᵥ (gram 𝕜 v) *ᵥ x := by
    simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def]
    rfl

theorem gram_eq' [RCLike 𝕜]
[SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E][Fintype n] {v : n → E} (x : n → 𝕜) :
    ⟪∑ i, x i • v i, ∑ i, x i • v i⟫ = star x ⬝ᵥ (gram 𝕜 v) *ᵥ x := by
  calc
  ⟪∑ i, x i • v i, ∑ i, x i • v i⟫
      = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ⟪v i, v j⟫) := by
    simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]
  _ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ((gram 𝕜 v) i j)) := by
    simp_rw [gram_apply]
  _ = star x ⬝ᵥ (gram 𝕜 v) *ᵥ x := by
    simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def]
    rfl

section PosSemidef

variable [RCLike 𝕜] [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A Gram matrix is positive semidefinite. -/
theorem gram_posSemidef [Fintype n] {v : n → E} :
    PosSemidef (gram 𝕜 v) := by
  refine ⟨isHermitian_gram, fun x ↦ ?_⟩
  rw [← gram_eq', le_iff_re_im]
  simp only [map_zero, inner_self_im, and_true]
  exact inner_self_nonneg

example (P Q : Prop) : (P → Q) ↔ (¬Q → ¬ P) := by exact Iff.symm not_imp_not

end PosSemidef

section PosDef

variable [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- A Gram matrix `gram 𝕜 v` is positive definite iff `v` is linearly independent. -/
theorem gram_posDef_iff_linearIndependent [Fintype n] {v : n → E} :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v:= by
  rw [Fintype.linearIndependent_iff]
  obtain ⟨h0, h1⟩ := gram_posSemidef (𝕜 := 𝕜) (v := v)
  refine ⟨fun h y hy ↦ ?_, fun h ↦ ⟨h0, fun x hx ↦ lt_of_le_of_ne (h1 x) ?_⟩⟩
  · obtain ⟨h1, h2⟩ := h
    specialize h2 y
    rw [← gram_eq', ← not_imp_not, ne_eq, Decidable.not_not, RCLike.pos_iff,
      ← norm_sq_eq_re_inner] at h2
    apply funext_iff.mp
    apply h2
    simp [hy]
  · specialize h x
    rw [← funext_iff, ← not_imp_not] at h
    simp_rw [← gram_eq']
    intro j
    apply h hx
    rw [← norm_eq_zero]
    obtain j1 := congrArg (⇑re) j
    rw [map_zero, ← norm_sq_eq_re_inner] at j1
    obtain j1' := Eq.symm j1
    rw [← sq_eq_zero_iff.symm] at j1'
    exact j1'

end PosDef

end Matrix

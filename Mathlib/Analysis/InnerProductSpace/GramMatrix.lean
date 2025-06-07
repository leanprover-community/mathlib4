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

lemma gram_apply [Inner 𝕜 E] {v : n → E} (i j : n) :
    (gram _ v) i j = ⟪v i, v j⟫ := by
  rfl

variable [RCLike 𝕜]

/-- A Gram matrix is Hermitian. -/
lemma isHermitian_gram
[SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E] {v : n → E} : (gram 𝕜 v).IsHermitian := by
  refine IsHermitian.ext_iff.mpr (fun i j ↦ ?_)
  rw [gram, of_apply, of_apply]
  simp only [RCLike.star_def, inner_conj_symm]

section SemiInnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

theorem star_dotProduct_gram_mulVec [Fintype n] {v : n → E} (x : n → 𝕜) :
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ x = ⟪∑ i, x i • v i, ∑ i, x i • v i⟫ := by
  calc
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ x =
    (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ((gram 𝕜 v) i j)) := by
      simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def]
      rfl
    _ = (∑ (i : n), ∑ (j : n), (starRingEnd 𝕜) (x i) * (x j) * ⟪v i, v j⟫) := by
      simp_rw [gram_apply]
    _ = ⟪∑ i, x i • v i, ∑ i, x i • v i⟫ := by
      simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

/-- A Gram matrix is positive semidefinite. -/
theorem gram_posSemidef [Fintype n] {v : n → E} :
    PosSemidef (gram 𝕜 v) := by
  refine ⟨isHermitian_gram, fun x ↦ ?_⟩
  rw [star_dotProduct_gram_mulVec, le_iff_re_im]
  simp only [map_zero, inner_self_im, and_true]
  exact inner_self_nonneg

/-- In a seminormed space, positive definiteness of `gram 𝕜 v` implies linear independence of `v` -/
theorem linearIndependent_of_gram_posDef [Fintype n] {v : n → E} (h_gram : PosDef (gram 𝕜 v)) :
    LinearIndependent 𝕜 v:= by
  rw [Fintype.linearIndependent_iff]
  obtain ⟨h0, h1⟩ := gram_posSemidef (𝕜 := 𝕜) (v := v)
  intro y hy
  obtain ⟨h1, h2⟩ := h_gram
  specialize h2 y
  rw [star_dotProduct_gram_mulVec, ← not_imp_not, ne_eq, Decidable.not_not, RCLike.pos_iff,
    ← norm_sq_eq_re_inner] at h2
  apply funext_iff.mp
  apply h2
  simp [hy]

end SemiInnerProductSpace

section NormedInnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a normed space, linear independence of `v` implies positive definiteness of `gram 𝕜 v`. -/
theorem gram_posDef_of_linearIndependent  [Fintype n]
    {v : n → E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v) := by
  rw [Fintype.linearIndependent_iff] at h_li
  obtain ⟨h0, h1⟩ := gram_posSemidef (𝕜 := 𝕜) (v := v)
  refine ⟨h0, fun x hx ↦ lt_of_le_of_ne (h1 x) ?_⟩
  specialize h_li x
  rw [← funext_iff, ← not_imp_not] at h_li
  simp_rw [star_dotProduct_gram_mulVec]
  intro j
  apply h_li hx
  rw [← norm_eq_zero]
  obtain j1 := congrArg (⇑re) j
  rw [map_zero, ← norm_sq_eq_re_inner] at j1
  obtain j1' := Eq.symm j1
  rw [← sq_eq_zero_iff.symm] at j1'
  exact j1'

/-- In a normed space, linear independence of `v` is equivalent to positive definiteness of
`gram 𝕜 v`. -/
theorem gram_posDef_iff_linearIndependent [Fintype n] {v : n → E}  :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v :=
  ⟨linearIndependent_of_gram_posDef, gram_posDef_of_linearIndependent⟩

end NormedInnerProductSpace

end Matrix

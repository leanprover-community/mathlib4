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

* `Matrix.posSemidef_gram` Gram matrices are positive semi-definite.
* `Matrix.posDef_gram_iff_linearIndependent` Linear independence of `v` is
  equivalent to positive definiteness of `gram 𝕜 v`.
-/

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {E n : Type*}
variable {α : Type*}
variable {𝕜 : Type*}
namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n → E) : Matrix n n 𝕜 := of fun i j ↦ ⟪v i, v j⟫_𝕜

@[simp]
lemma gram_apply [Inner 𝕜 E] (v : n → E) (i j : n) :
    (gram _ v) i j = ⟪v i, v j⟫_𝕜 := rfl

variable [RCLike 𝕜]

section SemiInnerProductSpace

variable [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

@[simp]
lemma gram_zero : gram 𝕜 (0 : n → E) = 0 := Matrix.ext fun _ _ ↦ inner_zero_left _

@[simp]
lemma gram_single [DecidableEq n] (i : n) (x : E) :
    gram 𝕜 (Pi.single i x) = Matrix.single i i ⟪x, x⟫_𝕜 := by
  ext j k
  obtain hij | rfl := ne_or_eq i j
  · simp [hij]
  obtain hik | rfl := ne_or_eq i k
  · simp [hik]
  simp

variable (𝕜) in
/-- A Gram matrix is Hermitian. -/
lemma isHermitian_gram (v : n → E) : (gram 𝕜 v).IsHermitian :=
  Matrix.ext fun _ _ ↦ inner_conj_symm _ _

theorem star_dotProduct_gram_mulVec [Fintype n] {v : n → E} (x : n → 𝕜) :
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ x = ⟪∑ i, x i • v i, ∑ i, x i • v i⟫_𝕜 := by
  trans ∑ i, ∑ j, conj (x i) * x j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

variable (𝕜) in
/-- A Gram matrix is positive semidefinite. -/
theorem posSemidef_gram [Fintype n] (v : n → E) :
    PosSemidef (gram 𝕜 v) := by
  refine ⟨isHermitian_gram _ _, fun x ↦ ?_⟩
  rw [star_dotProduct_gram_mulVec, le_iff_re_im]
  simp only [map_zero, inner_self_im, and_true, inner_self_nonneg]

/-- In a seminormed space, positive definiteness of `gram 𝕜 v` implies linear independence of `v` -/
theorem linearIndependent_of_posDef_gram [Fintype n] {v : n → E} (h_gram : PosDef (gram 𝕜 v)) :
    LinearIndependent 𝕜 v := by
  rw [Fintype.linearIndependent_iff]
  intro y hy
  obtain ⟨h1, h2⟩ := h_gram
  specialize h2 y
  rw [star_dotProduct_gram_mulVec, ← not_imp_not, ne_eq, Decidable.not_not, RCLike.pos_iff,
    ← norm_sq_eq_re_inner, hy] at h2
  apply funext_iff.mp
  apply h2
  simp

end SemiInnerProductSpace

section NormedInnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a normed space, linear independence of `v` implies positive definiteness of `gram 𝕜 v`. -/
theorem posDef_gram_of_linearIndependent  [Fintype n]
    {v : n → E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v) := by
  rw [Fintype.linearIndependent_iff] at h_li
  obtain ⟨h0, h1⟩ := posSemidef_gram (𝕜 := 𝕜) (v := v)
  refine ⟨h0, fun x hx ↦ (h1 x).lt_of_ne' ?_⟩
  specialize h_li x
  rw [← funext_iff, ← not_imp_not] at h_li
  simp_rw [star_dotProduct_gram_mulVec]
  intro hz
  apply h_li hx
  rw [← norm_eq_zero]
  have j1 := congrArg re hz
  rwa [map_zero, ← norm_sq_eq_re_inner, sq_eq_zero_iff] at j1

/-- In a normed space, linear independence of `v` is equivalent to positive definiteness of
`gram 𝕜 v`. -/
theorem posDef_gram_iff_linearIndependent [Fintype n] {v : n → E} :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v :=
  ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

end NormedInnerProductSpace

end Matrix

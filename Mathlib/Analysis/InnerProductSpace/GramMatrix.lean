/-
Copyright (c) 2025 Peter Pfaffelhuber. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Peter Pfaffelhuber
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Matrix.PosDef

import Mathlib.Analysis.Matrix.Order

/-! # Gram Matrices

This file defines Gram matrices and proves their positive semidefiniteness.
Results require `RCLike 𝕜`.

## Main definition

* `Matrix.gram` : the `Matrix n n 𝕜` with `⟪v i, v j⟫` at `i j : n`, where `v : n → E` for an
  `Inner 𝕜 E`.

## Main results

* `Matrix.posSemidef_gram`: Gram matrices are positive semidefinite.
* `Matrix.posDef_gram_iff_linearIndependent`: Linear independence of `v` is
  equivalent to positive definiteness of `gram 𝕜 v`.
-/

@[expose] public section

open RCLike Real Matrix

open scoped InnerProductSpace ComplexOrder ComplexConjugate

variable {E n α 𝕜 : Type*}
namespace Matrix

/-- The entries of a Gram matrix are inner products of vectors in an inner product space. -/
def gram (𝕜 : Type*) [Inner 𝕜 E] (v : n → E) : Matrix n n 𝕜 := of fun i j ↦ ⟪v i, v j⟫_𝕜

@[simp]
lemma gram_apply [Inner 𝕜 E] (v : n → E) (i j : n) :
    (gram 𝕜 v) i j = ⟪v i, v j⟫_𝕜 := rfl

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

lemma submatrix_gram (v : n → E) {m : Type*} (f : m → n) :
    (gram 𝕜 v).submatrix f f = gram 𝕜 (v ∘ f) := rfl

variable (𝕜) in
/-- A Gram matrix is Hermitian. -/
lemma isHermitian_gram (v : n → E) : (gram 𝕜 v).IsHermitian :=
  Matrix.ext fun _ _ ↦ inner_conj_symm _ _

theorem star_dotProduct_gram_mulVec [Fintype n] (v : n → E) (x y : n → 𝕜) :
    star x ⬝ᵥ (gram 𝕜 v) *ᵥ y = ⟪∑ i, x i • v i, ∑ i, y i • v i⟫_𝕜 := by
  trans ∑ i, ∑ j, conj (x i) * y j * ⟪v i, v j⟫_𝕜
  · simp_rw [dotProduct, mul_assoc, ← Finset.mul_sum, mulVec, dotProduct, mul_comm, ← star_def,
      gram_apply, Pi.star_apply]
  · simp_rw [sum_inner, inner_sum, inner_smul_left, inner_smul_right, mul_assoc]

open scoped ComplexConjugate in
private theorem linearCombination_inner_linearCombination_eq (v : n → E) (x y : n →₀ 𝕜) :
    ⟪x.linearCombination 𝕜 v, y.linearCombination 𝕜 v⟫_𝕜 =
      (x.sum fun i xi ↦ y.sum fun j yj ↦ conj xi * ⟪v i, v j⟫_𝕜 * yj) := by
  simp_rw [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, ← mul_assoc, mul_right_comm _ (inner _ _ _)]

variable (𝕜) in
/-- A Gram matrix is positive semidefinite. -/
theorem posSemidef_gram (v : n → E) : PosSemidef (gram 𝕜 v) :=
  ⟨isHermitian_gram _ _, by simp [← linearCombination_inner_linearCombination_eq]⟩

/-- In a normed space, positive definiteness of `gram 𝕜 v` implies linear independence of `v`. -/
theorem linearIndependent_of_posDef_gram {v : n → E} (h_gram : PosDef (gram 𝕜 v)) :
    LinearIndependent 𝕜 v := by
  refine linearIndependent_iff.mpr fun l hl ↦ ?_
  by_contra
  simpa [hl, ← linearCombination_inner_linearCombination_eq] using h_gram.2 this

theorem linearIndependent_of_det_gram_ne_zero [Fintype n] [DecidableEq n] {v : n → E}
    (h : (gram 𝕜 v).det ≠ 0) : LinearIndependent 𝕜 v :=
  linearIndependent_of_posDef_gram <| (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero.mpr h

end SemiInnerProductSpace

section NormedInnerProductSpace
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- In a normed space, linear independence of `v` implies positive definiteness of `gram 𝕜 v`. -/
theorem posDef_gram_of_linearIndependent
    {v : n → E} (h_li : LinearIndependent 𝕜 v) : PosDef (gram 𝕜 v) := by
  refine ⟨isHermitian_gram _ _, fun x hx ↦ ((posSemidef_gram 𝕜 v).2 x).lt_of_ne' ?_⟩
  simp_rw [star_def, gram_apply, ← linearCombination_inner_linearCombination_eq (𝕜 := 𝕜)]
  simp [mt (linearIndependent_iff.mp h_li x) hx]

/-- In a normed space, linear independence of `v` is equivalent to positive definiteness of
`gram 𝕜 v`. -/
theorem posDef_gram_iff_linearIndependent {v : n → E} :
    PosDef (gram 𝕜 v) ↔ LinearIndependent 𝕜 v :=
  ⟨linearIndependent_of_posDef_gram, posDef_gram_of_linearIndependent⟩

theorem det_gram_ne_zero_iff_linearIndependent [Fintype n] [DecidableEq n] {v : n → E} :
    (gram 𝕜 v).det ≠ 0 ↔ LinearIndependent 𝕜 v := by
  rw [← posDef_gram_iff_linearIndependent, (posSemidef_gram 𝕜 v).posDef_iff_det_ne_zero]

theorem gram_eq_conjTranspose_mul {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι 𝕜 E) (v : n → E) :
    letI m := of fun i j ↦ b.repr (v j) i
    gram 𝕜 v = mᴴ * m := by
  ext i j
  simp [Matrix.mul_apply, b.repr_apply_apply, b.sum_inner_mul_inner]

@[simp]
lemma gram_eq_one_iff_orthonormal [DecidableEq n] {v : n → E} : gram 𝕜 v = 1 ↔ Orthonormal 𝕜 v := by
  simp [← Matrix.ext_iff, orthonormal_iff_ite, Matrix.one_apply]

/-- Inequality `‖f x‖ ≤ ‖f‖ * ‖x‖` lifted to Gram matrices. -/
theorem posSemidef_opNorm_smul_gram_sub_gram {F} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    (v : n → E) (f : E →L[𝕜] F) : (‖f‖ ^ 2 • gram 𝕜 v - gram 𝕜 (f ∘ v)).PosSemidef := by
  refine posSemidef_iff_submatrix_finset.mpr fun s ↦ ?_
  simp only [submatrix_sub, submatrix_smul, Pi.sub_apply, Pi.smul_apply, submatrix_gram]
  refine .of_dotProduct_mulVec_nonneg
    (((isHermitian_gram 𝕜 _).smul (by simp [IsSelfAdjoint])).sub (isHermitian_gram 𝕜 _)) fun x ↦ ?_
  simp only [sub_mulVec, smul_mulVec, dotProduct_sub, dotProduct_smul,
    star_dotProduct_gram_mulVec, Function.comp_apply, ← map_smul, ← map_sum,
    inner_self_eq_norm_sq_to_K, sub_nonneg]
  norm_cast
  simpa only [smul_eq_mul, ← mul_pow] using pow_le_pow_left₀ (norm_nonneg _) (f.le_opNorm _) 2

end NormedInnerProductSpace

end Matrix

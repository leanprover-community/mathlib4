/-
Copyright (c) 2025 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/

import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Canoncial tensors in real inner product spaces

Given an `InnerProductSpace ℝ E`, this file defines two canonical tensors.

* `InnerProductSpace.canonicalContravariantTensor E : E ⊗[ℝ] E →ₗ[ℝ] ℝ`. This is
  the element corresponding to the inner product.

* If `E` is finite-dimensional, then `E ⊗[ℝ] E` is canonically isomorphic to its
  dual. Accordingly, there exists an element
  `InnerProductSpace.canonicalCovariantTensor E : E ⊗[ℝ] E` that corresponds to
  `InnerProductSpace.canonicalContravariantTensor E` under this identification.

The theorem `InnerProductSpace.canonicalCovariantTensorRepresentation` shows
that `InnerProductSpace.canonicalCovariantTensor E` can be computed from any
orthonormal basis `v` as `∑ i, (v i) ⊗ₜ[ℝ] (v i)`.
-/

open InnerProductSpace TensorProduct

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The canonical contravariant tensor corresponding to the inner product -/
noncomputable def InnerProductSpace.canonicalContravariantTensor :
    E ⊗[ℝ] E →ₗ[ℝ] ℝ := lift bilinFormOfRealInner

/-- The canonical covariant tensor corresponding to `InnerProductSpace.canonicalContravariantTensor`
under the identification of `E` with its dual -/
noncomputable def InnerProductSpace.canonicalCovariantTensor [FiniteDimensional ℝ E] :
    E ⊗[ℝ] E := ∑ i, ((stdOrthonormalBasis ℝ E) i) ⊗ₜ[ℝ] ((stdOrthonormalBasis ℝ E) i)

/-- Representation of the canonical covariant tensor in terms of an orthonormal basis. -/
theorem InnerProductSpace.canonicalCovariantTensorRepresentation [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (v : OrthonormalBasis ι ℝ E) :
    InnerProductSpace.canonicalCovariantTensor E = ∑ i, (v i) ⊗ₜ[ℝ] (v i) := by
  let w := stdOrthonormalBasis ℝ E
  conv =>
    right; arg 2; intro i; rw [← w.sum_repr' (v i)]
  simp_rw [sum_tmul, tmul_sum, smul_tmul_smul]
  conv =>
    right; rw [Finset.sum_comm]
    arg 2; intro y; rw [Finset.sum_comm]
    arg 2; intro x; rw [← Finset.sum_smul]
    arg 1; arg 2; intro i; rw [← real_inner_comm (w x)]
  simp_rw [OrthonormalBasis.sum_inner_mul_inner v]
  have {i} : ∑ j, ⟪w i, w j⟫_ℝ • w i ⊗ₜ[ℝ] w j = w i ⊗ₜ[ℝ] w i := by
    rw [Fintype.sum_eq_single i, orthonormal_iff_ite.1 w.orthonormal]
    simp only [↓reduceIte, one_smul]
    intro _ _
    simp only [orthonormal_iff_ite.1 w.orthonormal, ite_smul, one_smul, zero_smul,
      ite_eq_right_iff]
    tauto
  simp_rw [this]
  rfl

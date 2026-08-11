/-
Copyright (c) 2025 Matteo Cipollina. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Analysis of stochastic matrices

This file contains analytic consequences of `Matrix.rowStochastic` from
`Mathlib/LinearAlgebra/Matrix/Stochastic.lean`: operator-norm and spectral-radius bounds.

## Main statements

* `Matrix.linfty_opNorm_le_one_of_mem_rowStochastic`: a row-stochastic matrix has `L∞` operator
  norm at most `1`.
* `Matrix.norm_mulVec_le_of_mem_rowStochastic`: a row-stochastic matrix is nonexpansive for
  `Matrix.mulVec`.
* `Matrix.spectralRadius_le_one_of_mem_rowStochastic`: a row-stochastic matrix has spectral radius
  at most `1`.

-/

@[expose] public section

namespace Matrix

variable {𝕜 n : Type*} {A : Matrix n n 𝕜} [RCLike 𝕜] [Fintype n]

open scoped ComplexOrder Matrix.Norms.Operator

lemma linfty_opNorm_le_one_of_row_sum (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) : ‖A‖ ≤ 1 := by
  have h (i : n) : ∑ j, ‖A i j‖₊ = 1 := by
    rw [← NNReal.coe_inj, ← RCLike.ofReal_inj (K := 𝕜)]
    push_cast [RCLike.norm_of_nonneg' (h_nonneg i _)]
    exact h_row_sum i
  simp [linfty_opNorm_def, Finset.sup_le_iff, h]

lemma norm_mulVec_le_of_row_sum (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) (v : n → 𝕜) : ‖A *ᵥ v‖ ≤ ‖v‖ := by
  grw [linfty_opNorm_mulVec, linfty_opNorm_le_one_of_row_sum h_row_sum h_nonneg, one_mul]

variable [DecidableEq n]

lemma linfty_opNorm_le_one_of_mem_rowStochastic (hM : A ∈ rowStochastic 𝕜 n) : ‖A‖ ≤ 1 :=
  linfty_opNorm_le_one_of_row_sum (sum_row_of_mem_rowStochastic hM) fun _ _ =>
    nonneg_of_mem_rowStochastic hM

lemma norm_mulVec_le_of_mem_rowStochastic (hM : A ∈ rowStochastic 𝕜 n) (v : n → 𝕜) :
    ‖A *ᵥ v‖ ≤ ‖v‖ := by
  grw [linfty_opNorm_mulVec, linfty_opNorm_le_one_of_mem_rowStochastic hM, one_mul]

theorem spectralRadius_le_one_of_mem_rowStochastic [Nonempty n] (hM : A ∈ rowStochastic 𝕜 n) :
    spectralRadius 𝕜 A ≤ 1 :=
  (spectrum.spectralRadius_le_nnnorm A).trans <| by
    exact_mod_cast linfty_opNorm_le_one_of_mem_rowStochastic hM

theorem spectralRadius_le_one_of_row_sum [Nonempty n] (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) : spectralRadius 𝕜 A ≤ 1 :=
  spectralRadius_le_one_of_mem_rowStochastic (mem_rowStochastic_iff_sum.mpr ⟨h_nonneg, h_row_sum⟩)

end Matrix

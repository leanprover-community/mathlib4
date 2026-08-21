/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
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

open scoped ComplexOrder Matrix.Norms.Operator

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

theorem linfty_opNorm_le_one_of_mem_rowStochastic (hA : A ∈ rowStochastic 𝕜 n) : ‖A‖ ≤ 1 := by
  have hrow (i : n) : ∑ j, ‖A i j‖ = 1 := RCLike.ofReal_injective (K := 𝕜) <| by
    push_cast [RCLike.norm_of_nonneg' (nonneg_of_mem_rowStochastic hA)]
    exact sum_row_of_mem_rowStochastic hA i
  simp [linfty_opNorm_def, ← NNReal.coe_le_coe, hrow]

theorem norm_mulVec_le_of_mem_rowStochastic (hA : A ∈ rowStochastic 𝕜 n) (v : n → 𝕜) :
    ‖A *ᵥ v‖ ≤ ‖v‖ := by
  grw [linfty_opNorm_mulVec, linfty_opNorm_le_one_of_mem_rowStochastic hA, one_mul]

theorem spectralRadius_le_one_of_mem_rowStochastic [Nonempty n] (hA : A ∈ rowStochastic 𝕜 n) :
    spectralRadius 𝕜 A ≤ 1 :=
  (spectrum.spectralRadius_le_nnnorm A).trans <|
    mod_cast linfty_opNorm_le_one_of_mem_rowStochastic hA

end Matrix

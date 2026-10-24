/-
Copyright (c) 2025 Matteo Cipollina, Michail Karatarakis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Michail Karatarakis
-/
module

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandRadius
public import Mathlib.Analysis.Normed.Algebra.Spectrum
public import Mathlib.LinearAlgebra.Matrix.Stochastic

import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Analysis of stochastic matrices

This file contains analytic consequences of `Matrix.rowStochastic` and `Matrix.colStochastic` from
`Mathlib/LinearAlgebra/Matrix/Stochastic.lean`: operator-norm, spectral-radius and Gelfand-radius
bounds. Norms are the `L∞` operator norm, from `Matrix.Norms.Operator`.

## Main statements

* `Matrix.linfty_opNorm_le_one_of_mem_rowStochastic`: a row-stochastic matrix has `L∞` operator
  norm at most `1`.
* `Matrix.norm_mulVec_le_of_mem_rowStochastic`: a row-stochastic matrix is nonexpansive for
  `Matrix.mulVec`.
* `Matrix.spectralRadius_le_one_of_mem_rowStochastic`,
  `Matrix.spectralRadius_le_one_of_mem_colStochastic`: a row- or column-stochastic matrix has
  spectral radius at most `1`.
* `Matrix.gelfandRadius_le_one_of_mem_rowStochastic`,
  `Matrix.gelfandRadius_le_one_of_mem_colStochastic`: a row- or column-stochastic matrix has
  Gelfand radius at most `1`. For a real matrix, this bounds the moduli of all its complex
  eigenvalues, whereas `spectralRadius ℝ` only sees the real ones.
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

theorem spectralRadius_le_one_of_mem_rowStochastic (hA : A ∈ rowStochastic 𝕜 n) :
    spectralRadius 𝕜 A ≤ 1 :=
  (spectralRadius_le_nnnorm A).trans <|
    mod_cast linfty_opNorm_le_one_of_mem_rowStochastic hA

theorem spectralRadius_le_one_of_mem_colStochastic (hA : A ∈ colStochastic 𝕜 n) :
    spectralRadius 𝕜 A ≤ 1 := by
  simpa [spectralRadius_eq_of_unital, spectrum_transpose] using
    spectralRadius_le_one_of_mem_rowStochastic
      (transpose_mem_rowStochastic_iff_mem_colStochastic.2 hA)

theorem gelfandRadius_le_one_of_mem_rowStochastic (hA : A ∈ rowStochastic 𝕜 n) :
    gelfandRadius A ≤ 1 :=
  (gelfandRadius_le_norm A).trans (linfty_opNorm_le_one_of_mem_rowStochastic hA)

theorem gelfandRadius_le_one_of_mem_colStochastic (hA : A ∈ colStochastic 𝕜 n) :
    gelfandRadius A ≤ 1 := by
  refine gelfandRadius_le_of_bound (C := Fintype.card n) zero_le_one fun k ↦ ?_
  have hk := pow_mem hA k
  have hle (i j : n) : ‖(A ^ k) i j‖ ≤ 1 := by
    have : (A ^ k) i j ≤ 1 := le_one_of_mem_colStochastic hk
    rw [← RCLike.norm_of_nonneg' (nonneg_of_mem_colStochastic hk)] at this
    exact_mod_cast this
  rw [one_pow, mul_one, linfty_opNorm_def, ← NNReal.coe_natCast, NNReal.coe_le_coe]
  refine Finset.sup_le fun i _ ↦ ?_
  simpa using Finset.sum_le_card_nsmul Finset.univ (fun j ↦ ‖(A ^ k) i j‖₊) 1
    fun j _ ↦ mod_cast hle i j

end Matrix

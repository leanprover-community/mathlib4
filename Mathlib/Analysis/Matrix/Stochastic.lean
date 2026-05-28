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

-/

@[expose] public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]
variable {A : Matrix n n ℝ}

open scoped Matrix.Norms.Operator

omit [DecidableEq n] in
/-- Auxiliary form of `norm_mulVec_le_of_mem_rowStochastic` using row sums. -/
lemma norm_mulVec_le_of_row_sum (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) : ∀ v : n → ℝ, ‖A *ᵥ v‖ ≤ ‖v‖ := by
  intro v
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro i
  rw [Real.norm_eq_abs, Matrix.mulVec]
  calc |∑ j, A i j * v j|
    _ ≤ ∑ j, |A i j * v j| :=
      Finset.abs_sum_le_sum_abs (fun i_1 ↦ A i i_1 * v i_1) Finset.univ
    _ = ∑ j, (A i j) * |v j| := by simp_rw [abs_mul, abs_of_nonneg (h_nonneg i _)]
    _ ≤ ∑ j, A i j * ‖v‖ := Finset.sum_le_sum fun j _ =>
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (h_nonneg i j)
    _ = (∑ j, A i j) * ‖v‖ := (Finset.sum_mul ..).symm
    _ = ‖v‖ := by rw [h_row_sum i, one_mul]

/-- A row-stochastic matrix is nonexpansive for `mulVec` in the `L∞` operator norm.
Also `‖A *ᵥ v‖ ≤ ‖A‖ * ‖v‖` by `Matrix.linfty_opNorm_mulVec`. -/
lemma norm_mulVec_le_of_mem_rowStochastic (hM : A ∈ rowStochastic ℝ n) :
    ∀ v : n → ℝ, ‖A *ᵥ v‖ ≤ ‖v‖ := by
  rw [mem_rowStochastic_iff_sum] at hM
  exact norm_mulVec_le_of_row_sum hM.2 hM.1

/-- A row-stochastic matrix has `L∞` operator norm at most `1` (`Matrix.linfty_opNorm_def`). -/
lemma linfty_opNorm_le_one_of_mem_rowStochastic (hM : A ∈ rowStochastic ℝ n) : ‖A‖ ≤ 1 := by
  let f := ContinuousLinearMap.mk (Matrix.mulVecLin A)
  have h_mulVec : ∀ v, ‖f v‖ ≤ ‖v‖ := fun v => by
    dsimp [f]
    exact norm_mulVec_le_of_mem_rowStochastic hM v
  simpa [linfty_opNorm_eq_opNorm] using f.opNorm_le_bound zero_le_one fun v => by
    dsimp [f]
    rw [one_mul]
    exact h_mulVec v

/-- The spectral radius of a row-stochastic matrix is at most `1`, via
`spectrum.spectralRadius_le_nnnorm`. -/
theorem spectralRadius_le_one_of_mem_rowStochastic [Nonempty n] (hM : A ∈ rowStochastic ℝ n) :
    spectralRadius ℝ A ≤ 1 := by
  refine (spectrum.spectralRadius_le_nnnorm (𝕜 := ℝ) A).trans ?_
  rw [← ENNReal.coe_one]
  exact ENNReal.coe_le_coe.mpr (by simpa using linfty_opNorm_le_one_of_mem_rowStochastic hM)

/-- See `spectralRadius_le_one_of_mem_rowStochastic`. -/
theorem spectralRadius_le_one_of_row_sum [Nonempty n] (h_row_sum : ∀ i, ∑ j, A i j = 1)
    (h_nonneg : ∀ i j, 0 ≤ A i j) : spectralRadius ℝ A ≤ 1 :=
  spectralRadius_le_one_of_mem_rowStochastic (mem_rowStochastic_iff_sum.mpr ⟨h_nonneg, h_row_sum⟩)

end Matrix

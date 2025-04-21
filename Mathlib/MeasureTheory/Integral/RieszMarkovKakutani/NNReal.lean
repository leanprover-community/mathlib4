/-
Copyright (c) 2025 Yoh Tanimioto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/

import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
#  Riesz–Markov–Kakutani representation theorem for `NNReal`

This file will prove the Riesz-Markov-Kakutani representation theorem on a locally compact
T2 space `X` for `NNReal`-linear functionals `Λ`.

The measure is first defined through `rieszContent` for `toNNRealLinear`-version of `Λ`.
The result is first proved for `Real`-linear Λ because in a standard proof one has to prove the
inequalities by `le_antisymm`, yet for `C_c(X, ℝ≥0)` there is no `Neg`.

## References

* [Walter Rudin, Real and Complex Analysis.][Rud87]

-/

noncomputable section

open scoped NNReal

open CompactlySupported CompactlySupportedContinuousMap MeasureTheory

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X]
  [BorelSpace X]
variable (Λ : C_c(X, ℝ≥0) →ₗ[ℝ≥0] ℝ≥0)

namespace NNRealRMK

theorem lintegral_rieszMeasure_eq (f : C_c(X, ℝ≥0)) : ∫⁻ (x : X), f x ∂(rieszMeasure Λ) = Λ f := by
  rw [lintegral_coe_eq_integral, ← ENNReal.ofNNReal_toNNReal]
  · simp only [ENNReal.coe_inj]
    rw [Real.toNNReal_of_nonneg (by apply integral_nonneg; intro x; simp),
      ← NNReal.coe_inj, ← eq_toRealLinear_toReal f,
      ← RealRMK.integral_rieszMeasure (nonneg_toRealLinear Λ) f.toReal]
    · simp only [toReal_apply, NNReal.coe_mk]
      congr
      exact Eq.symm (eq_toNNRealLinear_toRealLinear Λ)
  rw [rieszMeasure]
  exact Continuous.integrable_of_hasCompactSupport (by continuity)
    (HasCompactSupport.comp_left f.hasCompactSupport rfl)

end NNRealRMK

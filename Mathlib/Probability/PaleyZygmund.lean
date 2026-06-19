/-
Copyright (c) 2026 Yanxin Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yanxin Zhou
-/
module


public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!

# Paley–Zygmund inequality
This file contains the *Paley-Zygmund inequality* which states that,
given a nonnegative random variable Z with finite variance, if 0 ≤ θ ≤ 1,
then P(Z > θ EZ) ≥ (1-θ)^2 (EZ)^2/EZ^2. The proof uses Cauchy-Schwarz inequality.

## Main Result
- `ProbabilityTheory.paley_zygmund`: the Paley-Zygmund inequality.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}


/-- **The Paley-Zygmund Inequality**: If `Z≥ 0` is a random variable with finite variance, and if
`0≤ θ ≤ 1`, then `P(Z>θ EZ) ≥ (1-θ)^2 (EZ)^2/E(Z^2)`.
-/
theorem paley_zygmund [IsProbabilityMeasure μ] {Z: Ω → ℝ} (hZ_nn : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ)
  {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤ (∫ ω, Z ω ^ 2 ∂μ)
  * (μ {ω | θ * ∫ ω', Z ω' ∂μ < Z ω}).toReal := by
  have h_split: ∫ ω, Z ω ∂μ = ∫ ω in {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}, Z ω ∂μ
    + ∫ ω in {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}ᶜ, Z ω ∂μ := sorry
  have h_lower: (1 - θ) * (∫ ω, Z ω ∂μ) ≤ ∫ ω in {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}, Z ω ∂μ:= sorry
  have h_cs: (∫ ω in {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}, Z ω ∂μ) ^ 2 ≤
    (∫ ω, Z ω ^ 2 ∂μ ) * (μ {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}).toReal:= sorry
  calc
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 = ((1 - θ) * (∫ ω, Z ω ∂μ)) ^ 2 := by ring
    _ ≤ (∫ ω in {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}, Z ω ∂μ) ^ 2 := by
      apply pow_le_pow_left₀ sorry h_lower
    _ ≤ (∫ ω, Z ω ^ 2 ∂μ ) * (μ {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}).toReal:= h_cs


end ProbabilityTheory

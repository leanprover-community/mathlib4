/-
Copyright (c) 2026 Yanxin Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yanxin Zhou
-/
module


public import Mathlib.Probability.Moments.Variance
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.Mul

/-!

# Paley–Zygmund inequality
This file contains the *Paley-Zygmund inequality* which states that,
given a nonnegative random variable Z with finite variance, if 0 ≤ θ ≤ 1,
then P(Z > θ EZ) ≥ (1-θ)^2 (EZ)^2/EZ^2. The proof uses Jensen's inequality.

## Main Result
- `ProbabilityTheory.paley_zygmund`: the Paley-Zygmund inequality.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The Paley-Zygmund Inequality**: If `Z ≥ 0` is a random variable with finite variance, and if
`0 ≤ θ ≤ 1`, then `P(Z > θ * EZ) ≥ (1-θ)^2 (EZ)^2/E(Z^2)`.
-/
theorem paley_zygmund [IsProbabilityMeasure μ] {Z : Ω → ℝ} (hZ_nn : 0 ≤ᵐ[μ] Z) (hZ2 : MemLp Z 2 μ)
  {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) : (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 ≤ (∫ ω, Z ω ^ 2 ∂μ)
  * (μ {ω | θ * ∫ ω', Z ω' ∂μ < Z ω}).toReal := by
  let S := {ω | θ * (∫ ω', Z ω' ∂μ) < Z ω}
  have hZ_int := hZ2.integrable one_le_two
  have hZ_int_nn := integral_nonneg_of_ae hZ_nn
  have h_split: ∫ ω, Z ω ∂μ = ∫ ω in S, Z ω ∂μ + ∫ ω in Sᶜ, Z ω ∂μ :=
    (integral_add_compl₀ (nullMeasurableSet_lt aemeasurable_const
    hZ2.aemeasurable) hZ_int).symm
  have h_lower: (1 - θ) * (∫ ω, Z ω ∂μ) ≤ ∫ ω in S, Z ω ∂μ:= by
    have h_bound_comp: ∫ ω in Sᶜ, Z ω ∂μ ≤ θ * ∫ ω, Z ω ∂μ := by
      calc
        ∫ ω in Sᶜ, Z ω ∂μ ≤ ∫ ω in Sᶜ, θ * (∫ ω', Z ω' ∂μ) ∂μ:=
          setIntegral_mono_on₀
            (hf := hZ_int.integrableOn)
            (hg := integrableOn_const)
            (nullMeasurableSet_lt aemeasurable_const hZ2.aemeasurable).compl
            (fun ω hω => by simp only [S, Set.mem_compl_iff, Set.mem_setOf, not_lt] at hω; exact hω)
        _ ≤ θ * ∫ ω, Z ω ∂μ := by
          rw [setIntegral_const, smul_eq_mul]
          apply mul_le_of_le_one_left (mul_nonneg hθ0 hZ_int_nn)
            measureReal_le_one
    linarith [h_split, h_bound_comp]
  have h_cs: (∫ ω in S, Z ω ∂μ) ^ 2 ≤
    (∫ ω, Z ω ^ 2 ∂μ ) * (μ S).toReal:= by
    by_cases hS : μ S = 0
    · simp [Measure.restrict_eq_zero.mpr, hS]
    · have h_jensen := ConvexOn.map_set_average_le
        even_two.convexOn_pow
        (continuous_pow 2).continuousOn
        isClosed_univ
        hS
        (measure_ne_top μ S)
        (by simp)
        hZ_int.integrableOn
        hZ2.integrable_sq.integrableOn
      have hμS_pos : 0 < μ.real S := by
        rw [measureReal_def]
        exact ENNReal.toReal_pos hS (measure_ne_top μ S)
      rw [setAverage_eq, setAverage_eq, smul_eq_mul, smul_eq_mul, mul_pow, sq ((μ.real S)⁻¹),
      mul_assoc, mul_le_mul_iff_of_pos_left (inv_pos.mpr hμS_pos), mul_comm,
      ← div_eq_mul_inv, div_le_iff₀ hμS_pos, measureReal_def] at h_jensen
      calc
        (∫ ω in S, Z ω ∂μ) ^ 2 ≤ (∫ ω in S, Z ω ^ 2 ∂μ) * (μ S).toReal := h_jensen
        _ ≤ (∫ ω, Z ω ^ 2 ∂μ) * (μ S).toReal :=
          mul_le_mul_of_nonneg_right
            (setIntegral_le_integral hZ2.integrable_sq (ae_of_all μ (fun x => sq_nonneg (Z x))))
            ENNReal.toReal_nonneg
  calc
    (1 - θ) ^ 2 * (∫ ω, Z ω ∂μ) ^ 2 = ((1 - θ) * (∫ ω, Z ω ∂μ)) ^ 2 := by ring
    _ ≤ (∫ ω in S, Z ω ∂μ) ^ 2 := by
      apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr hθ1) hZ_int_nn) h_lower
    _ ≤ (∫ ω, Z ω ^ 2 ∂μ ) * (μ S).toReal:= h_cs


end ProbabilityTheory

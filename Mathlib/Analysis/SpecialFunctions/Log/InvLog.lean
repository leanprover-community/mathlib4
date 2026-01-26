/-
Copyright (c) 2025 Alastair Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alastair Irving, Michael Stoll
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Multiplicative inverse of real logarithm

We prove properties of the function `x ↦ (log x)⁻¹`.

## Main results

- `deriv_inv_log` gives a formula for the derivative which holds for all values.
-/

public section

namespace Real

open Filter

lemma not_differentiableAt_inv_log_zero : ¬ DifferentiableAt ℝ (fun x ↦ (log x)⁻¹) 0 := by
  simp only [← hasDerivAt_deriv_iff, hasDerivAt_iff_tendsto_slope_zero, zero_add, log_zero,
    inv_zero, sub_zero, smul_eq_mul, ← mul_inv, mul_comm _ (log _)]
  have H' : Tendsto (fun x ↦ log x * x) (nhdsWithin 0 (Set.Iio 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      tendsto_log_mul_self_nhdsLT_zero ?_
    simp only [← nhdsWithin_Ioo_eq_nhdsLT neg_one_lt_zero, Set.mem_Ioi]
    refine eventually_nhdsWithin_of_forall fun x ⟨hx₁, hx₂⟩ ↦ mul_pos_of_neg_of_neg ?_ hx₂
    refine log_neg_eq_log x ▸ log_neg ?_ ?_ <;> grind
  exact fun H ↦ (tendsto_nhdsWithin_mono_left (show Set.Iio (0 : ℝ) ⊆ _ by grind) H).not_tendsto
    (by simp) (tendsto_inv_nhdsGT_zero.comp H')

lemma not_continuousAt_inv_log_one : ¬ ContinuousAt (fun x ↦ (log x)⁻¹) 1 := by
  suffices Tendsto (fun x ↦ (log x)⁻¹) (nhdsWithin 1 {1}ᶜ) (Bornology.cobounded ℝ) from
    not_continuousAt_of_tendsto this nhdsWithin_le_nhds (Metric.disjoint_nhds_cobounded _)
  have H := HasDerivAt.tendsto_nhdsNE (by simpa using hasDerivAt_log one_ne_zero) one_ne_zero
  exact tendsto_inv₀_nhdsNE_zero.comp <| log_one ▸ H

lemma not_continuousAt_inv_log_neg_one : ¬ ContinuousAt (fun x ↦ (log x)⁻¹) (-1) := by
  refine fun H ↦ not_continuousAt_inv_log_one ?_
  simpa only [log_neg_eq_log] using ContinuousAt.comp' H continuousAt_neg

theorem deriv_inv_log {x : ℝ} :
    deriv (fun x ↦ (log x)⁻¹) x = -x⁻¹ / (log x ^ 2) := by
  rcases eq_or_ne x 0 with rfl | h0
  · simpa using deriv_zero_of_not_differentiableAt not_differentiableAt_inv_log_zero
  rcases eq_or_ne x 1 with rfl | h1
  · simpa using deriv_zero_of_not_differentiableAt <|
      mt DifferentiableAt.continuousAt not_continuousAt_inv_log_one
  rcases eq_or_ne x (-1) with rfl | h2
  · simpa using deriv_zero_of_not_differentiableAt <|
      mt DifferentiableAt.continuousAt not_continuousAt_inv_log_neg_one
  simp_all

end Real

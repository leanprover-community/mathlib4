/-
Copyright (c) 2025 Moritz Doll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Doll
-/
import Mathlib.Analysis.Distribution.SchwartzSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# The Dirac delta


-/

open MeasureTheory MeasureTheory.Measure Filter Topology BoundedContinuousFunction

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
variable (μ : Measure E) [μ.IsAddHaarMeasure]
variable (φ : C(E, ℝ))

/-- For `φ : E → ℝ` with `∫ x, φ x ∂μ = 1` and `f : E →ᵇ F`, we have that
`∫ n ^ d • φ(n • x) • f x ∂μ` converges to `f 0` as `n → ∞`.

The more common variant is `∫ ε ^ (-d) • φ(ε⁻¹ • x) • f x ∂μ` converges to `f 0` as `ε → 0`. -/
theorem foo (f : E →ᵇ F) (hφ_int : ∫ x, φ x ∂μ = 1) :
    Tendsto (fun n : ℝ ↦ ∫ x, (n ^ Module.finrank ℝ E) • φ (n • x) • f x ∂ μ)
      atTop (𝓝 (f 0)) := by
  have h₁ : (fun n : ℝ ↦ ∫ x, (n ^ Module.finrank ℝ E) • φ (n • x) • f x ∂ μ)
      =ᶠ[atTop] fun n ↦ ∫ x, φ x • f (n⁻¹ • x) ∂ μ := by
    rw [EventuallyEq, eventually_atTop]
    use 1
    intro n hn
    rw [integral_smul, ← integral_comp_inv_smul_of_nonneg _ _ (by positivity)]
    congr
    ext x
    congr
    rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ (by positivity), one_smul]
  have h₂ : ∫ x, φ x • f 0 ∂μ = f 0 := by rw [integral_smul_const, hφ_int, one_smul]
  rw [Filter.tendsto_congr' h₁, ← h₂]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖φ x‖ * ‖f‖)
  · filter_upwards with n
    exact (φ.continuous.smul <| f.continuous.comp <| continuous_const_smul _).aestronglyMeasurable
  · filter_upwards with n
    filter_upwards with x
    rw [norm_smul]
    gcongr
    apply norm_coe_le_norm
  · apply Integrable.mul_const
    have hφ' := integrable_of_integral_eq_one hφ_int
    rwa [integrable_norm_iff hφ'.aestronglyMeasurable]
  filter_upwards with x
  apply Tendsto.const_smul <| Tendsto.comp (f.continuousAt 0) _
  rw [← zero_smul ℝ x]
  exact tendsto_inv_atTop_zero.smul_const _

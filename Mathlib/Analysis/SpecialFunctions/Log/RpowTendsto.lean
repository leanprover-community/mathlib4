/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithm as a limit of powers

This file shows that the logarithm can be expressed as a limit of powers, namely that
`p⁻¹ * (x ^ p - 1)` tends to `log x` as `p` tends to zero for positive `x`.

## Main declarations

* `tendstoUniformlyOn_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)` tends uniformly to `log x` on
  compact subsets of `Ioi 0` as `p` tends to zero
* `tendsto_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)`: the analogous statement for pointwise
  convergence.
-/

open scoped Topology
open Real Filter

open Set in
lemma tendstoUniformlyOn_rpow_sub_one_log {s : Set ℝ} (hs : s ⊆ Ioi 0) (hs' : IsCompact s) :
    TendstoUniformlyOn (fun (p : ℝ) (x : ℝ) => p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) s := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let pbound : ℝ := ε / (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1)
  have hxs : ∀ x ∈ s, x ≠ 0 := by grind
  have sSup_nonneg : 0 ≤ sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [norm_nonneg, ← sq_nonneg]
  have sSup_nonneg' : 0 ≤ sSup ((fun x => ‖log x‖) '' s) := by
    refine Real.sSup_nonneg ?_
    grind [norm_nonneg, ← sq_nonneg]
  have pbound_pos : 0 < pbound := by positivity
  have h₁ : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p := eventually_mem_of_tendsto_nhdsWithin fun ⦃U⦄ a => a
  have h₂ : ∀ᶠ p : ℝ in 𝓝[>] 0, p < pbound :=
    Eventually.filter_mono nhdsWithin_le_nhds <| eventually_lt_nhds pbound_pos
  have h₃ : ∀ᶠ p : ℝ in 𝓝[>] 0, p ≤ 1 / (sSup ((fun x => ‖log x‖) '' s) + 1) :=
    Eventually.filter_mono nhdsWithin_le_nhds <| eventually_le_nhds (by positivity)
  have hcont : ContinuousOn (fun x => ‖log x‖ ^ 2) s := by
    fun_prop (disch := assumption)
  have hcont' : ContinuousOn (fun x => ‖log x‖) s := by
    fun_prop (disch := assumption)
  filter_upwards [h₁, h₂, h₃] with p hp₁ hp₂ hp₃
  have p_nonneg : 0 ≤ p := by grind
  intro x hx
  have hx' : ‖p * log x‖ ≤ 1 := calc
    _ = p * ‖log x‖ := by grind [norm_mul, Real.norm_of_nonneg]
    _ ≤ 1 / (sSup ((fun y => ‖log y‖) '' s) + 1) * ‖log x‖ := by gcongr
    _ ≤ 1 / (‖log x‖ + 1) * ‖log x‖ := by
        gcongr
        refine le_csSup ?_ (by grind)
        grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ = ‖log x‖ / (‖log x‖ + 1) := by grind
    _ ≤ 1 := by rw [div_le_one₀] <;> grind [norm_nonneg]
  have pinv_nonneg : 0 ≤ p⁻¹ := by grind [_root_.inv_nonneg]
  rw [dist_eq_norm']
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
          simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
          congr
          rw [mul_comm, Real.exp_mul, Real.exp_log (by grind)]
    _ ≤ p⁻¹ * ‖p * log x‖ ^ 2 := by
          gcongr
          refine Real.norm_exp_sub_one_sub_id_le ?_
          simp only [hx']
    _ = p * ‖log x‖ ^ 2 := by
          simp only [norm_mul]
          grind [Real.norm_of_nonneg]
    _ ≤ p * sSup ((fun x => ‖log x‖ ^ 2) '' s) := by
          gcongr
          refine le_csSup ?_ (by grind)
          grind [IsCompact.bddAbove, ← IsCompact.image_of_continuousOn]
    _ ≤ p * (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1) := by gcongr; grind
    _ < pbound * (sSup ((fun x => ‖log x‖ ^ 2) '' s) + 1) := by gcongr
    _ = ε := by grind

lemma tendsto_rpow_sub_one_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p => p⁻¹ * (x ^ p - 1)) (𝓝[>] 0) (𝓝 (log x)) :=
  TendstoUniformlyOn.tendsto_at (s := {x})
    (tendstoUniformlyOn_rpow_sub_one_log (by grind) isCompact_singleton) (by grind)

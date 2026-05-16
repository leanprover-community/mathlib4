/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The logarithm as a limit of powers

This file shows that the logarithm can be expressed as a limit of powers, namely that
`p⁻¹ * (x ^ p - 1)` tends to `log x` as `p` tends to zero for positive `x`.

## Main declarations

* `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)` tends uniformly to
  `log x` on compact subsets of `Ioi 0` as `p` tends to zero
* `tendsto_rpow_sub_one_log`: `p⁻¹ * (x ^ p - 1)`: the analogous statement for pointwise
  convergence.
-/

public section

open scoped Topology
open Real Filter

lemma Real.norm_inv_mul_rpow_sub_one_sub_log_le {p x : ℝ} (p_pos : 0 < p) (x_pos : 0 < x)
    (hx : ‖p * log x‖ ≤ 1) : ‖p⁻¹ * (x ^ p - 1) - log x‖ ≤ p * ‖log x‖ ^ 2 := by
  have pinv_nonneg : 0 ≤ p⁻¹ := by grind [_root_.inv_nonneg]
  calc
    _ = ‖p⁻¹ * ((x ^ p - 1) - p * log x)‖ := by grind
    _ = p⁻¹ * ‖(rexp (p * log x) - 1) - p * log x‖ := by
          simp only [norm_mul, Real.norm_of_nonneg (r := p⁻¹) pinv_nonneg]
          congr
          rw [mul_comm, Real.exp_mul, Real.exp_log (by grind)]
    _ ≤ p⁻¹ * ‖p * log x‖ ^ 2 := by
          gcongr
          refine Real.norm_exp_sub_one_sub_id_le ?_
          simp only [hx]
    _ = p * ‖log x‖ ^ 2 := by
          simp only [norm_mul]
          grind [Real.norm_of_nonneg]

open Set in
lemma Real.tendstoLocallyUniformlyOn_rpow_sub_one_log :
    TendstoLocallyUniformlyOn (fun (p : ℝ) (x : ℝ) => p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) (Ioi 0) := by
  refine (tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi).mpr ?_
  intro s hs hs'
  rw [Metric.uniformity_basis_dist_le.tendstoUniformlyOn_iff_of_uniformity]
  intro ε hε
  obtain ⟨logbound, hlogbound⟩ := hs'.exists_bound_of_continuousOn (f := Real.log)
    (Real.continuousOn_log.mono fun _ hx => ne_of_gt (hs hx))
  let logbound : ℝ := max logbound 0
  let pbound : ℝ := ε / (logbound ^ 2 + 1)
  have pbound_pos : 0 < pbound := by positivity
  have h₁ : ∀ᶠ p : ℝ in 𝓝[>] 0, 0 < p ∧ p < pbound := nhdsGT_basis 0 |>.mem_of_mem pbound_pos
  have h₂ : ∀ᶠ p : ℝ in 𝓝[>] 0, p ≤ 1 / (logbound + 1) :=
    Eventually.filter_mono nhdsWithin_le_nhds <| eventually_le_nhds (by positivity)
  filter_upwards [h₁, h₂] with p ⟨hp₁,hp₂⟩ hp₃
  intro x hx
  have hxlog : ‖log x‖ ≤ logbound := (hlogbound x hx).trans (le_max_left _ _)
  have hx' : ‖p * log x‖ ≤ 1 := calc
    _ = p * ‖log x‖ := by grind [norm_mul, Real.norm_of_nonneg]
    _ ≤ 1 / (logbound + 1) * ‖log x‖ := by gcongr
    _ ≤ 1 / (‖log x‖ + 1) * ‖log x‖ := by
        gcongr
    _ = ‖log x‖ / (‖log x‖ + 1) := by grind
    _ ≤ 1 := by rw [div_le_one₀] <;> grind [norm_nonneg]
  rw [dist_eq_norm']
  calc
    _ ≤ p * ‖log x‖ ^ 2 := Real.norm_inv_mul_rpow_sub_one_sub_log_le hp₁ (hs hx) hx'
    _ ≤ p * logbound ^ 2 := by gcongr
    _ ≤ pbound * (logbound ^ 2 + 1) := by gcongr; grind
    _ = ε := by
      dsimp [pbound]
      field_simp

lemma tendsto_rpow_sub_one_log {x : ℝ} (hx : 0 < x) :
    Tendsto (fun p => p⁻¹ * (x ^ p - 1)) (𝓝[>] 0) (𝓝 (log x)) :=
  TendstoLocallyUniformlyOn.tendsto_at
    tendstoLocallyUniformlyOn_rpow_sub_one_log (by grind)

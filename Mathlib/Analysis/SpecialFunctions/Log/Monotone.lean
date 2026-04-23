/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# Logarithm Tonality

In this file we describe the tonality of the logarithm function when multiplied by functions of the
form `x ^ a`.

## Tags

logarithm, tonality
-/

public section


open Set Filter Function

open Topology

noncomputable section

namespace Real

theorem mul_log_strictMonoOn : StrictMonoOn (fun x ↦ x * log x) <| .Ici <| exp (-1) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) continuous_mul_log.continuousOn fun x hx ↦ ?_
  have hlt : rexp (-1) < x := by simpa using hx
  have hpos : 0 < x := by grind [Real.exp_pos]
  grind [deriv_mul_log, Real.lt_log_iff_exp_lt hpos |>.mpr hlt]

@[deprecated Real.mul_log_strictMonoOn (since := "2026-04-07")]
theorem log_mul_self_monotoneOn : MonotoneOn (fun x : ℝ => log x * x) { x | 1 ≤ x } := by
  grind [mul_log_strictMonoOn.monotoneOn, MonotoneOn.mono, show exp (-1) < 1 by norm_num]

theorem mul_log_strictAntiOn :
    StrictAntiOn (fun x : ℝ ↦ x * log x) <| .Icc 0 (exp (-1)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc ..) continuous_mul_log.continuousOn fun x hx ↦ ?_
  have hgt : x < rexp (-1) := by simp_all [interior_Icc, mem_Ioo]
  have hpos : 0 < x := by simp_all [interior_Icc, mem_Ioo]
  grind [deriv_mul_log, Real.log_lt_iff_lt_exp hpos |>.mpr hgt]

theorem log_div_self_antitoneOn : AntitoneOn (fun x : ℝ ↦ log x / x) <| .Ici (exp 1) := by
  intro x hex y hey hxy
  have x_pos : 0 < x := (exp_pos 1).trans_le hex
  have y_pos : 0 < y := (exp_pos 1).trans_le hey
  have hlogx : 1 ≤ log x := by rwa [le_log_iff_exp_le x_pos]
  have hyx : 0 ≤ y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff₀ x_pos, zero_add, one_mul]
  rw [div_le_iff₀ y_pos, ← sub_le_sub_iff_right (log x)]
  calc
    log y - log x = log (y / x) := by rw [log_div y_pos.ne' x_pos.ne']
    _ ≤ y / x - 1 := log_le_sub_one_of_pos (div_pos y_pos x_pos)
    _ ≤ log x * (y / x - 1) := le_mul_of_one_le_left hyx hlogx
    _ = log x / x * y - log x := by ring

theorem log_div_self_rpow_antitoneOn {a : ℝ} (ha : 0 < a) :
    AntitoneOn (fun x : ℝ ↦ log x / x ^ a) <| .Ici (exp a⁻¹) := by
  intro x hex y _ hxy
  simp only
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos a⁻¹) (le_of_le_of_eq hex rfl)
  have y_pos : 0 < y := by linarith
  nth_rw 1 [← rpow_one y, ← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm, div_eq_mul_one_div a a, rpow_mul y_pos.le, rpow_mul x_pos.le,
    log_rpow (rpow_pos_of_pos y_pos a), log_rpow (rpow_pos_of_pos x_pos a), mul_div_assoc,
    mul_div_assoc, mul_le_mul_iff_right₀ (one_div_pos.mpr ha)]
  have hbound {z : ℝ} (hz : rexp (1 / a) ≤ z) : z ^ a ∈ {b | rexp 1 ≤ b} := by
    rw [mem_setOf_eq]
    convert rpow_le_rpow _ hz (le_of_lt ha) using 1
    · simp only [← exp_mul, Real.exp_eq_exp, field]
    positivity
  refine log_div_self_antitoneOn (hbound hex) (hbound (hex.trans hxy)) ?_
  gcongr

theorem log_div_sqrt_antitoneOn : AntitoneOn (fun x : ℝ ↦ log x / √x) <| .Ici (exp 2) := by
  simp_rw [sqrt_eq_rpow]
  convert log_div_self_rpow_antitoneOn one_half_pos
  norm_num

end Real

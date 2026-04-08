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
  simp only [StrictMonoOn]
  intro x hex y hey _
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y,
      deriv (fun x ↦ x * Real.log x) c = (y * Real.log y - x * Real.log x) / (y - x) := by
    apply_rules [exists_deriv_eq_slope]
    · exact continuousOn_of_forall_continuousAt fun z hz ↦
        ContinuousAt.mul continuousAt_id
          (Real.continuousAt_log (by linarith [hz.1, Real.exp_pos (-1), hex.out, hey.out]))
    · exact DifferentiableOn.mul differentiableOn_id
        (DifferentiableOn.log differentiableOn_id fun z hz ↦
          ne_of_gt <| lt_trans (Real.exp_pos _) <| hex.out.trans_lt hz.1)
  have hc_ge_inve : c > Real.exp (-1) := by linarith [hc.1.1, hex.out]
  have c_ne0 : c ≠ 0 := ne_of_gt <| lt_trans (Real.exp_pos _) hc_ge_inve
  rw [deriv_mul_log c_ne0, eq_div_iff] at hc
    <;> nlinarith [Real.log_exp (-1), Real.log_lt_log (by positivity) hc_ge_inve]

@[deprecated "use `Real.mul_log_StrictMonoOn`" (since := "2026-04-07")]
theorem log_mul_self_monotoneOn : MonotoneOn (fun x : ℝ => log x * x) { x | 1 ≤ x } := by
  grind [mul_log_StrictMonoOn.monotoneOn, MonotoneOn.mono, show exp (-1) < 1 by norm_num]

theorem mul_log_StrictAntiOn :
    StrictAntiOn (fun x : ℝ ↦ x * log x) (Set.Icc 0 (exp (-1))) := by
  simp only [StrictAntiOn]
  intro x hex y hey hxy
  obtain ⟨c, hc⟩ : ∃ c ∈ Set.Ioo x y,
      deriv (fun x : ℝ ↦ x * log x) c = (y * log y - x * log x) / (y - x) := by
    apply_rules [exists_deriv_eq_slope]
    · simp_all [Continuous.continuousOn Real.continuous_mul_log]
    · exact DifferentiableOn.mono Real.differentiableOn_mul_log (by simp_all)
  have hc_pos : 0 < c := by linarith [hc.1.1, hex.1]
  norm_num [hc_pos.ne'] at hc
  rw [eq_div_iff] at hc <;>
    nlinarith [Real.log_exp (-1),
      Real.log_lt_log (by positivity) (by linarith [hex.2, hey.2] : c < Real.exp (-1))]

theorem log_div_self_antitoneOn : AntitoneOn (fun x : ℝ ↦ log x / x) { x | exp 1 ≤ x } := by
  simp only [AntitoneOn, mem_setOf_eq]
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
    AntitoneOn (fun x : ℝ ↦ log x / x ^ a) { x | exp (1 / a) ≤ x } := by
  simp only [AntitoneOn, mem_setOf_eq]
  intro x hex y _ hxy
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos (1 / a)) hex
  have y_pos : 0 < y := by linarith
  nth_rw 1 [← rpow_one y]
  nth_rw 1 [← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm, div_eq_mul_one_div a a, rpow_mul y_pos.le, rpow_mul x_pos.le,
    log_rpow (rpow_pos_of_pos y_pos a), log_rpow (rpow_pos_of_pos x_pos a), mul_div_assoc,
    mul_div_assoc, mul_le_mul_iff_right₀ (one_div_pos.mpr ha)]
  refine log_div_self_antitoneOn ?_ ?_ ?_
  · simp only [Set.mem_setOf_eq]
    convert rpow_le_rpow _ hex (le_of_lt ha) using 1
    · rw [← exp_mul]
      simp only [Real.exp_eq_exp]
      field
    positivity
  · simp only [Set.mem_setOf_eq]
    convert rpow_le_rpow _ (_root_.trans hex hxy) (le_of_lt ha) using 1
    · rw [← exp_mul]
      simp only [Real.exp_eq_exp]
      field
    positivity
  gcongr

theorem log_div_sqrt_antitoneOn : AntitoneOn (fun x : ℝ ↦ log x / √x) { x | exp 2 ≤ x } := by
  simp_rw [sqrt_eq_rpow]
  convert log_div_self_rpow_antitoneOn one_half_pos
  norm_num

end Real

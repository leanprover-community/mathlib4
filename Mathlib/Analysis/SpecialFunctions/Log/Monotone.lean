/-
Copyright (c) 2021 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

#align_import analysis.special_functions.log.monotone from "leanprover-community/mathlib"@"0b9eaaa7686280fad8cce467f5c3c57ee6ce77f8"

/-!
# Logarithm Tonality

In this file we describe the tonality of the logarithm function when multiplied by functions of the
form `x ^ a`.

## Tags

logarithm, tonality
-/


open Set Filter Function

open Topology

noncomputable section

namespace Real

variable {x y : ℝ}

theorem log_mul_self_monotoneOn : MonotoneOn (fun x : ℝ => log x * x) { x | 1 ≤ x } := by
  -- TODO: can be strengthened to exp (-1) ≤ x
  simp only [MonotoneOn, mem_setOf_eq]
  intro x hex y hey hxy
  have y_pos : 0 < y := lt_of_lt_of_le zero_lt_one hey
  gcongr
  rwa [le_log_iff_exp_le y_pos, Real.exp_zero]
#align real.log_mul_self_monotone_on Real.log_mul_self_monotoneOn

theorem log_div_self_antitoneOn : AntitoneOn (fun x : ℝ => log x / x) { x | exp 1 ≤ x } := by
  simp only [AntitoneOn, mem_setOf_eq]
  intro x hex y hey hxy
  have x_pos : 0 < x := (exp_pos 1).trans_le hex
  have y_pos : 0 < y := (exp_pos 1).trans_le hey
  have hlogx : 1 ≤ log x := by rwa [le_log_iff_exp_le x_pos]
  have hyx : 0 ≤ y / x - 1 := by rwa [le_sub_iff_add_le, le_div_iff x_pos, zero_add, one_mul]
  rw [div_le_iff y_pos, ← sub_le_sub_iff_right (log x)]
  calc
    log y - log x = log (y / x) := by rw [log_div y_pos.ne' x_pos.ne']
    _ ≤ y / x - 1 := log_le_sub_one_of_pos (div_pos y_pos x_pos)
    _ ≤ log x * (y / x - 1) := le_mul_of_one_le_left hyx hlogx
    _ = log x / x * y - log x := by ring
#align real.log_div_self_antitone_on Real.log_div_self_antitoneOn

theorem log_div_self_rpow_antitoneOn {a : ℝ} (ha : 0 < a) :
    AntitoneOn (fun x : ℝ => log x / x ^ a) { x | exp (1 / a) ≤ x } := by
  simp only [AntitoneOn, mem_setOf_eq]
  intro x hex y _ hxy
  have x_pos : 0 < x := lt_of_lt_of_le (exp_pos (1 / a)) hex
  have y_pos : 0 < y := by linarith
  have x_nonneg : 0 ≤ x := le_trans (le_of_lt (exp_pos (1 / a))) hex
  have y_nonneg : 0 ≤ y := by linarith
  nth_rw 1 [← rpow_one y]
  nth_rw 1 [← rpow_one x]
  rw [← div_self (ne_of_lt ha).symm, div_eq_mul_one_div a a, rpow_mul y_nonneg, rpow_mul x_nonneg,
    log_rpow (rpow_pos_of_pos y_pos a), log_rpow (rpow_pos_of_pos x_pos a), mul_div_assoc,
    mul_div_assoc, mul_le_mul_left (one_div_pos.mpr ha)]
  refine log_div_self_antitoneOn ?_ ?_ ?_
  · simp only [Set.mem_setOf_eq]
    convert rpow_le_rpow _ hex (le_of_lt ha) using 1
    · rw [← exp_mul]
      simp only [Real.exp_eq_exp]
      field_simp [(ne_of_lt ha).symm]
    exact le_of_lt (exp_pos (1 / a))
  · simp only [Set.mem_setOf_eq]
    convert rpow_le_rpow _ (_root_.trans hex hxy) (le_of_lt ha) using 1
    · rw [← exp_mul]
      simp only [Real.exp_eq_exp]
      field_simp [(ne_of_lt ha).symm]
    exact le_of_lt (exp_pos (1 / a))
  gcongr
#align real.log_div_self_rpow_antitone_on Real.log_div_self_rpow_antitoneOn

theorem log_div_sqrt_antitoneOn : AntitoneOn (fun x : ℝ => log x / √x) { x | exp 2 ≤ x } := by
  simp_rw [sqrt_eq_rpow]
  convert @log_div_self_rpow_antitoneOn (1 / 2) (by norm_num)
  norm_num
#align real.log_div_sqrt_antitone_on Real.log_div_sqrt_antitoneOn

end Real

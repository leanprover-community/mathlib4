/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Defs

/-!

This file proves $\log(n+1) \le H_n \le 1 + \log(n)$ for all natural numbers $n$.

-/

open BigOperators

theorem log_add_one_le_harmonic (n : ℕ) :
    Real.log ↑(n+1) ≤ harmonic n := by
  calc _ = ∫ x in (1)..↑(n+1), x⁻¹ := ?_
       _ = ∫ x in (1:ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ ∑ d in Finset.Icc 1 n, (d:ℝ)⁻¹ := ?_
       _ = harmonic n := ?_
  · rw[integral_inv (by simp[(show ¬ (1:ℝ) ≤ 0 by norm_num)] )]; congr; ring
  · congr; norm_num
  · apply AntitoneOn.integral_le_sum_Ico (by norm_num)
    apply inv_antitoneOn_Icc_right
    norm_num
  · simp [harmonic_eq_sum_Icc]

theorem harmonic_le_one_add_log (n : ℕ) :
    harmonic n ≤ 1 + Real.log n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_coe_nat]
  rw [← Finset.sum_erase_add (Finset.Icc 1 n) _ (show 1 ∈ Finset.Icc 1 n by simp [hn] ), add_comm]
  gcongr
  · norm_num
  simp only [gt_iff_lt, Nat.lt_one_iff, Finset.mem_Icc, true_and, not_le, Finset.Icc_erase_left]
  calc
    ∑ d : ℕ in .Ico 2 (n + 1), (d : ℝ)⁻¹ = ∑ d in .Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = ∫ x in (1)..n, x⁻¹ := ?_
    _ = Real.log ↑n := ?_
  · congr; norm_num;
  · apply @AntitoneOn.sum_le_integral_Ico 2 (n + 1) fun x : ℝ => (x - 1)⁻¹
    · linarith [hn]
    apply sub_inv_antitoneOn_Icc_right; norm_num
  · convert intervalIntegral.integral_comp_sub_right _ 1
    · norm_num
    · simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel]
  convert integral_inv _
  · simp
  norm_num; simp[hn, show (0:ℝ) < 1 by norm_num]

theorem log_le_harmonic_floor (y : ℝ) (hy : 0 ≤ y) :
    Real.log y ≤ harmonic ⌊y⌋₊ := by
  by_cases h0 : y = 0
  · simp [h0]
  · calc _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
        _ ≤ _ := ?_
    · gcongr
      apply (Nat.le_ceil y).trans
      norm_cast
      exact Nat.ceil_le_floor_add_one y
    · apply log_add_one_le_harmonic

theorem harmonic_floor_le_one_add_log (y : ℝ) (hy : 1 ≤ y) :
    harmonic ⌊y⌋₊ ≤ 1 + Real.log y := by
  trans (1 + Real.log (⌊y⌋₊))
  · apply harmonic_le_one_add_log (⌊y⌋₊)
  gcongr
  · norm_cast; apply Nat.lt_of_succ_le; apply Nat.le_floor; norm_cast
  · apply Nat.floor_le; linarith

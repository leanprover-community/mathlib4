/-
Copyright (c) 2024 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.NumberTheory.Harmonic.Defs

/-!

This file proves $\log(n+1) \le H_n \le 1 + \log(n)$ for all natural numbers $n$.

-/

lemma harmonic_eq_sum_Icc {n : ℕ} : harmonic n = ∑ i ∈ Finset.Icc 1 n, (↑i)⁻¹ := by
  rw [harmonic, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun (i : ℕ) ↦ (i : ℚ)⁻¹) 0 n (c := 1)]
  simp only [Finset.Ico_add_one_right_eq_Icc]

theorem log_add_one_le_harmonic (n : ℕ) :
    Real.log ↑(n+1) ≤ harmonic n := by
  calc _ = ∫ x in (1 : ℕ)..↑(n+1), x⁻¹ := ?_
       _ ≤ ∑ d ∈ Finset.Icc 1 n, (d : ℝ)⁻¹ := ?_
       _ = harmonic n := ?_
  · rw [Nat.cast_one, integral_inv (by simp [(show ¬ (1 : ℝ) ≤ 0 by norm_num)]), div_one]
  · exact (inv_antitoneOn_Icc_right <| by norm_num).integral_le_sum_Ico (Nat.le_add_left 1 n)
  · simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]

theorem harmonic_le_one_add_log (n : ℕ) :
    harmonic n ≤ 1 + Real.log n := by
  by_cases hn0 : n = 0
  · simp [hn0]
  have hn : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
  simp_rw [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.sum_erase_add (Finset.Icc 1 n) _ (Finset.left_mem_Icc.mpr hn), add_comm,
    Nat.cast_one, inv_one]
  refine add_le_add_left ?_ 1
  simp only [Nat.lt_one_iff, Finset.mem_Icc, Finset.Icc_erase_left]
  calc ∑ d ∈ .Ico 2 (n + 1), (d : ℝ)⁻¹
    _ = ∑ d ∈ .Ico 2 (n + 1), (↑(d + 1) - 1)⁻¹ := ?_
    _ ≤ ∫ x in (2).. ↑(n + 1), (x - 1)⁻¹  := ?_
    _ = ∫ x in (1)..n, x⁻¹ := ?_
    _ = Real.log ↑n := ?_
  · simp_rw [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  · exact @AntitoneOn.sum_le_integral_Ico 2 (n + 1) (fun x : ℝ ↦ (x - 1)⁻¹) (by linarith [hn]) <|
      sub_inv_antitoneOn_Icc_right (by norm_num)
  · convert intervalIntegral.integral_comp_sub_right _ 1
    · norm_num
    · simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right]
  · convert integral_inv _
    · rw [div_one]
    · simp only [Nat.one_le_cast, hn, Set.uIcc_of_le, Set.mem_Icc, Nat.cast_nonneg,
        and_true, not_le, zero_lt_one]

theorem log_le_harmonic_floor (y : ℝ) (hy : 0 ≤ y) :
    Real.log y ≤ harmonic ⌊y⌋₊ := by
  by_cases h0 : y = 0
  · simp [h0]
  · calc
      _ ≤ Real.log ↑(Nat.floor y + 1) := ?_
      _ ≤ _ := log_add_one_le_harmonic _
    gcongr
    apply (Nat.le_ceil y).trans
    norm_cast
    exact Nat.ceil_le_floor_add_one y

theorem harmonic_floor_le_one_add_log (y : ℝ) (hy : 1 ≤ y) :
    harmonic ⌊y⌋₊ ≤ 1 + Real.log y := by
  refine (harmonic_le_one_add_log _).trans ?_
  gcongr
  · exact_mod_cast Nat.floor_pos.mpr hy
  · exact Nat.floor_le <| zero_le_one.trans hy

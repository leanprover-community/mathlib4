/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Joseph Myers
-/
import Mathlib.Data.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

#align_import data.complex.exponential_bounds from "leanprover-community/mathlib"@"402f8982dddc1864bd703da2d6e2ee304a866973"

/-!
# Bounds on specific values of the exponential
-/


namespace Real

open IsAbsoluteValue Finset CauSeq Complex

theorem exp_one_near_10 : |exp 1 - 2244083 / 825552| ≤ 1 / 10 ^ 10 := by
  apply exp_approx_start
  iterate 13 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  norm_num1
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  rw [_root_.abs_one, abs_of_pos] <;> norm_num1
#align real.exp_one_near_10 Real.exp_one_near_10

theorem exp_one_near_20 : |exp 1 - 363916618873 / 133877442384| ≤ 1 / 10 ^ 20 := by
  apply exp_approx_start
  iterate 21 refine exp_1_approx_succ_eq (by norm_num1; rfl) (by norm_cast) ?_
  norm_num1
  refine exp_approx_end' _ (by norm_num1; rfl) _ (by norm_cast) (by simp) ?_
  rw [_root_.abs_one, abs_of_pos] <;> norm_num1
#align real.exp_one_near_20 Real.exp_one_near_20

theorem exp_one_gt_d9 : 2.7182818283 < exp 1 :=
  lt_of_lt_of_le (by norm_num) (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)
#align real.exp_one_gt_d9 Real.exp_one_gt_d9

theorem exp_one_lt_d9 : exp 1 < 2.7182818286 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) (by norm_num)
#align real.exp_one_lt_d9 Real.exp_one_lt_d9

theorem exp_neg_one_gt_d9 : 0.36787944116 < exp (-1) := by
  rw [exp_neg, lt_inv _ (exp_pos _)]
  · refine lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 exp_one_near_10).1) ?_
    norm_num
  · norm_num
#align real.exp_neg_one_gt_d9 Real.exp_neg_one_gt_d9

theorem exp_neg_one_lt_d9 : exp (-1) < 0.3678794412 := by
  rw [exp_neg, inv_lt (exp_pos _)]
  · refine lt_of_lt_of_le ?_ (sub_le_comm.1 (abs_sub_le_iff.1 exp_one_near_10).2)
    norm_num
  · norm_num
#align real.exp_neg_one_lt_d9 Real.exp_neg_one_lt_d9

set_option tactic.skipAssignedInstances false in
theorem log_two_near_10 : |log 2 - 287209 / 414355| ≤ 1 / 10 ^ 10 := by
  suffices |log 2 - 287209 / 414355| ≤ 1 / 17179869184 + (1 / 10 ^ 10 - 1 / 2 ^ 34) by
    norm_num1 at *
    assumption
  have t : |(2⁻¹ : ℝ)| = 2⁻¹ := by rw [abs_of_pos]; norm_num
  have z := Real.abs_log_sub_add_sum_range_le (show |(2⁻¹ : ℝ)| < 1 by rw [t]; norm_num) 34
  rw [t] at z
  norm_num1 at z
  rw [one_div (2 : ℝ), log_inv, ← sub_eq_add_neg, _root_.abs_sub_comm] at z
  apply le_trans (_root_.abs_sub_le _ _ _) (add_le_add z _)
  simp_rw [sum_range_succ]
  norm_num
  rw [abs_of_pos] <;> norm_num
#align real.log_two_near_10 Real.log_two_near_10

theorem log_two_gt_d9 : 0.6931471803 < log 2 :=
  lt_of_lt_of_le (by norm_num1) (sub_le_comm.1 (abs_sub_le_iff.1 log_two_near_10).2)
#align real.log_two_gt_d9 Real.log_two_gt_d9

theorem log_two_lt_d9 : log 2 < 0.6931471808 :=
  lt_of_le_of_lt (sub_le_iff_le_add.1 (abs_sub_le_iff.1 log_two_near_10).1) (by norm_num)
#align real.log_two_lt_d9 Real.log_two_lt_d9

end Real

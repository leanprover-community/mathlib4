/-
Copyright (c) 2019 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Mario Carneiro
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

#align_import data.real.pi.bounds from "leanprover-community/mathlib"@"402f8982dddc1864bd703da2d6e2ee304a866973"

/-!
# Pi

This file contains lemmas which establish bounds on `real.pi`.
Notably, these include `pi_gt_sqrtTwoAddSeries` and `pi_lt_sqrtTwoAddSeries`,
which bound `π` using series;
numerical bounds on `π` such as `pi_gt_314`and `pi_lt_315` (more precise versions are given, too).

See also `Mathlib/Data/Real/Pi/Leibniz.lean` and `Mathlib/Data/Real/Pi/Wallis.lean` for infinite
formulas for `π`.
-/

local macro_rules | `($x ^ $y) => `(HPow.hPow $x $y) -- Porting note: See issue lean4#2220

-- Porting note: needed to add a lot of type ascriptions for lean to interpret numbers as reals.

open scoped Real

namespace Real

theorem pi_gt_sqrtTwoAddSeries (n : ℕ) :
    (2 : ℝ) ^ (n + 1) * sqrt (2 - sqrtTwoAddSeries 0 n) < π := by
  have : sqrt (2 - sqrtTwoAddSeries 0 n) / (2 : ℝ) * (2 : ℝ) ^ (n + 2) < π := by
    rw [← lt_div_iff, ← sin_pi_over_two_pow_succ]; apply sin_lt; apply div_pos pi_pos
    all_goals apply pow_pos; norm_num
  apply lt_of_le_of_lt (le_of_eq _) this
  -- ⊢ 2 ^ (n + 1) * sqrt (2 - sqrtTwoAddSeries 0 n) = sqrt (2 - sqrtTwoAddSeries 0 …
  rw [pow_succ _ (n + 1), ← mul_assoc, div_mul_cancel, mul_comm]; norm_num
  -- ⊢ 2 ≠ 0
                                                                  -- 🎉 no goals
#align real.pi_gt_sqrt_two_add_series Real.pi_gt_sqrtTwoAddSeries

theorem pi_lt_sqrtTwoAddSeries (n : ℕ) :
    π < (2 : ℝ) ^ (n + 1) * sqrt (2 - sqrtTwoAddSeries 0 n) + 1 / (4 : ℝ) ^ n := by
  have : π <
      (sqrt (2 - sqrtTwoAddSeries 0 n) / (2 : ℝ) + (1 : ℝ) / ((2 : ℝ) ^ n) ^ 3 / 4) *
      (2 : ℝ) ^ (n + 2) := by
    rw [← div_lt_iff, ← sin_pi_over_two_pow_succ]
    refine' lt_of_lt_of_le (lt_add_of_sub_right_lt (sin_gt_sub_cube _ _)) _
    · apply div_pos pi_pos; apply pow_pos; norm_num
    · rw [div_le_iff']
      · refine' le_trans pi_le_four _
        simp only [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, mul_one]
        apply pow_le_pow; norm_num; apply le_add_of_nonneg_left; apply Nat.zero_le
      · apply pow_pos; norm_num
    apply add_le_add_left; rw [div_le_div_right]
    rw [le_div_iff, ← mul_pow]
    refine' le_trans _ (le_of_eq (one_pow 3)); apply pow_le_pow_of_le_left
    · apply le_of_lt; apply mul_pos; apply div_pos pi_pos; apply pow_pos; norm_num; apply pow_pos
      norm_num
    rw [← le_div_iff]
    refine' le_trans ((div_le_div_right _).mpr pi_le_four) _; apply pow_pos; norm_num
    rw [pow_succ, pow_succ, ← mul_assoc, ← div_div]
    -- Porting note: removed `convert le_rfl`
    all_goals (repeat' apply pow_pos); norm_num
  apply lt_of_lt_of_le this (le_of_eq _); rw [add_mul]; congr 1
  -- ⊢ (sqrt (2 - sqrtTwoAddSeries 0 n) / 2 + 1 / (2 ^ n) ^ 3 / 4) * 2 ^ (n + 2) =  …
                                          -- ⊢ sqrt (2 - sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) + 1 / (2 ^ n) ^ 3 / 4 * 2  …
                                                        -- ⊢ sqrt (2 - sqrtTwoAddSeries 0 n) / 2 * 2 ^ (n + 2) = 2 ^ (n + 1) * sqrt (2 -  …
  · rw [pow_succ _ (n + 1), ← mul_assoc, div_mul_cancel, mul_comm]; norm_num
    -- ⊢ 2 ≠ 0
                                                                    -- 🎉 no goals
  rw [pow_succ, ← pow_mul, mul_comm n 2, pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num, pow_succ,
    pow_succ, ← mul_assoc (2 : ℝ), show (2 : ℝ) * 2 = 4 by norm_num, ← mul_assoc, div_mul_cancel,
    mul_comm ((2 : ℝ) ^ n), ← div_div, div_mul_cancel]
  apply pow_ne_zero; norm_num; norm_num
  -- ⊢ 2 ≠ 0
                     -- ⊢ 4 ≠ 0
                               -- 🎉 no goals
#align real.pi_lt_sqrt_two_add_series Real.pi_lt_sqrtTwoAddSeries

/-- From an upper bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`sqrtTwoAddSeries 0 n ≤ 2 - (a / 2 ^ (n + 1)) ^ 2)`, one can deduce the lower bound `a < π`
thanks to basic trigonometric inequalities as expressed in `pi_gt_sqrtTwoAddSeries`. -/
theorem pi_lower_bound_start (n : ℕ) {a}
    (h : sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n ≤ (2 : ℝ) - (a / (2 : ℝ) ^ (n + 1)) ^ 2) :
    a < π := by
  refine' lt_of_le_of_lt _ (pi_gt_sqrtTwoAddSeries n); rw [mul_comm]
  -- ⊢ a ≤ 2 ^ (n + 1) * sqrt (2 - sqrtTwoAddSeries 0 n)
                                                       -- ⊢ a ≤ sqrt (2 - sqrtTwoAddSeries 0 n) * 2 ^ (n + 1)
  refine' (div_le_iff (pow_pos (by norm_num) _ : (0 : ℝ) < _)).mp (le_sqrt_of_sq_le _)
  -- ⊢ (a / 2 ^ (n + 1)) ^ 2 ≤ 2 - sqrtTwoAddSeries 0 n
  rwa [le_sub_comm, show (0 : ℝ) = (0 : ℕ) / (1 : ℕ) by rw [Nat.cast_zero, zero_div]]
  -- 🎉 no goals
#align real.pi_lower_bound_start Real.pi_lower_bound_start

theorem sqrtTwoAddSeries_step_up (c d : ℕ) {a b n : ℕ} {z : ℝ} (hz : sqrtTwoAddSeries (c / d) n ≤ z)
    (hb : 0 < b) (hd : 0 < d) (h : (2 * b + a) * d ^ 2 ≤ c ^ 2 * b) :
    sqrtTwoAddSeries (a / b) (n + 1) ≤ z := by
  refine' le_trans _ hz; rw [sqrtTwoAddSeries_succ]; apply sqrtTwoAddSeries_monotone_left
  -- ⊢ sqrtTwoAddSeries (↑a / ↑b) (n + 1) ≤ sqrtTwoAddSeries (↑c / ↑d) n
                         -- ⊢ sqrtTwoAddSeries (sqrt (2 + ↑a / ↑b)) n ≤ sqrtTwoAddSeries (↑c / ↑d) n
                                                     -- ⊢ sqrt (2 + ↑a / ↑b) ≤ ↑c / ↑d
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
  -- ⊢ sqrt (2 + ↑a / ↑b) ≤ ↑c / ↑d
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
  -- ⊢ sqrt (2 + ↑a / ↑b) ≤ ↑c / ↑d
  rw [sqrt_le_left (div_nonneg c.cast_nonneg d.cast_nonneg), div_pow,
    add_div_eq_mul_add_div _ _ (ne_of_gt hb'), div_le_div_iff hb' (pow_pos hd' _)]
  exact_mod_cast h
  -- 🎉 no goals
#align real.sqrt_two_add_series_step_up Real.sqrtTwoAddSeries_step_up

section Tactic

open Lean Elab Tactic

/-- `numDen stx` takes a syntax expression `stx` and
* if it is of the form `a / b`, then it returns `some (a, b)`;
* otherwise it returns `none`.
-/
private def numDen : Syntax → Option (Syntax.Term × Syntax.Term)
  | `($a / $b) => some (a, b)
  | _          => none

/-- Create a proof of `a < π` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≤ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ a/2^(n+1)`. -/
elab "pi_lower_bound " "[" l:term,* "]" : tactic => do
  let rat_sep := l.elemsAndSeps
  let sep := rat_sep.getD 1 .missing
  let ratStx := rat_sep.filter (· != sep)
  let n := ← (toExpr ratStx.size).toSyntax
  let els := (ratStx.map numDen).reduceOption
  evalTactic (← `(tactic| apply pi_lower_bound_start $n))
  let _ := ← els.mapM fun (x, y) => do
      evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_up $x $y))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals (evalTactic (← `(tactic| norm_num1)))

end Tactic

/-- From a lower bound on `sqrtTwoAddSeries 0 n = 2 cos (π / 2 ^ (n+1))` of the form
`2 - ((a - 1 / 4 ^ n) / 2 ^ (n + 1)) ^ 2 ≤ sqrtTwoAddSeries 0 n`, one can deduce the upper bound
`π < a` thanks to basic trigonometric formulas as expressed in `pi_lt_sqrtTwoAddSeries`. -/
theorem pi_upper_bound_start (n : ℕ) {a}
    (h : (2 : ℝ) - ((a - 1 / (4 : ℝ) ^ n) / (2 : ℝ) ^ (n + 1)) ^ 2 ≤
        sqrtTwoAddSeries ((0 : ℕ) / (1 : ℕ)) n)
    (h₂ : (1 : ℝ) / (4 : ℝ) ^ n ≤ a) : π < a := by
  refine' lt_of_lt_of_le (pi_lt_sqrtTwoAddSeries n) _
  -- ⊢ 2 ^ (n + 1) * sqrt (2 - sqrtTwoAddSeries 0 n) + 1 / 4 ^ n ≤ a
  rw [← le_sub_iff_add_le, ← le_div_iff', sqrt_le_left, sub_le_comm]
  · rwa [Nat.cast_zero, zero_div] at h
    -- 🎉 no goals
  · exact div_nonneg (sub_nonneg.2 h₂) (pow_nonneg (le_of_lt zero_lt_two) _)
    -- 🎉 no goals
  · exact pow_pos zero_lt_two _
    -- 🎉 no goals
#align real.pi_upper_bound_start Real.pi_upper_bound_start

theorem sqrtTwoAddSeries_step_down (a b : ℕ) {c d n : ℕ} {z : ℝ}
    (hz : z ≤ sqrtTwoAddSeries (a / b) n) (hb : 0 < b) (hd : 0 < d)
    (h : a ^ 2 * d ≤ (2 * d + c) * b ^ 2) : z ≤ sqrtTwoAddSeries (c / d) (n + 1) := by
  apply le_trans hz; rw [sqrtTwoAddSeries_succ]; apply sqrtTwoAddSeries_monotone_left
  -- ⊢ sqrtTwoAddSeries (↑a / ↑b) n ≤ sqrtTwoAddSeries (↑c / ↑d) (n + 1)
                     -- ⊢ sqrtTwoAddSeries (↑a / ↑b) n ≤ sqrtTwoAddSeries (sqrt (2 + ↑c / ↑d)) n
                                                 -- ⊢ ↑a / ↑b ≤ sqrt (2 + ↑c / ↑d)
  apply le_sqrt_of_sq_le
  -- ⊢ (↑a / ↑b) ^ 2 ≤ 2 + ↑c / ↑d
  have hb' : 0 < (b : ℝ) := Nat.cast_pos.2 hb
  -- ⊢ (↑a / ↑b) ^ 2 ≤ 2 + ↑c / ↑d
  have hd' : 0 < (d : ℝ) := Nat.cast_pos.2 hd
  -- ⊢ (↑a / ↑b) ^ 2 ≤ 2 + ↑c / ↑d
  rw [div_pow, add_div_eq_mul_add_div _ _ (ne_of_gt hd'), div_le_div_iff (pow_pos hb' _) hd']
  -- ⊢ ↑a ^ 2 * ↑d ≤ (2 * ↑d + ↑c) * ↑b ^ 2
  exact_mod_cast h
  -- 🎉 no goals
#align real.sqrt_two_add_series_step_down Real.sqrtTwoAddSeries_step_down

section Tactic

open Lean Elab Tactic

/-- Create a proof of `π < a` for a fixed rational number `a`, given a witness, which is a
sequence of rational numbers `sqrt 2 < r 1 < r 2 < ... < r n < 2` satisfying the property that
`sqrt (2 + r i) ≥ r(i+1)`, where `r 0 = 0` and `sqrt (2 - r n) ≥ (a - 1/4^n) / 2^(n+1)`. -/
elab "pi_upper_bound " "[" l:term,* "]" : tactic => do
  let rat_sep := l.elemsAndSeps
  let sep := rat_sep.getD 1 .missing
  let ratStx := rat_sep.filter (· != sep)
  let n := ← (toExpr ratStx.size).toSyntax
  let els := (ratStx.map numDen).reduceOption
  evalTactic (← `(tactic| apply pi_upper_bound_start $n))
  let _ := ← els.mapM fun (x, y) => do
      evalTactic (← `(tactic| apply sqrtTwoAddSeries_step_down $x $y))
  evalTactic (← `(tactic| simp [sqrtTwoAddSeries]))
  allGoals (evalTactic (← `(tactic| norm_num1)))

end Tactic

theorem pi_gt_three : 3 < π := by
  pi_lower_bound [23/16]
  -- 🎉 no goals
#align real.pi_gt_three Real.pi_gt_three

theorem pi_gt_314 : 3.14 < π := by
  pi_lower_bound [99 / 70, 874 / 473, 1940 / 989, 1447 / 727]
  -- 🎉 no goals
#align real.pi_gt_314 Real.pi_gt_314

theorem pi_lt_315 : π < 3.15 := by
  pi_upper_bound [140 / 99, 279 / 151, 51 / 26, 412 / 207]
  -- 🎉 no goals
#align real.pi_lt_315 Real.pi_lt_315

theorem pi_gt_31415 : 3.1415 < π := by
  pi_lower_bound
        [11482 / 8119, 5401 / 2923, 2348 / 1197, 11367 / 5711, 25705 / 12868, 23235 / 11621]
#align real.pi_gt_31415 Real.pi_gt_31415

theorem pi_lt_31416 : π < 3.1416 := by
    pi_upper_bound
        [4756 / 3363, 101211 / 54775, 505534 / 257719, 83289 / 41846, 411278 / 205887,
          438142 / 219137, 451504 / 225769, 265603 / 132804, 849938 / 424971]
#align real.pi_lt_31416 Real.pi_lt_31416

theorem pi_gt_3141592 : 3.141592 < π := by
    pi_lower_bound
        [11482 / 8119, 7792 / 4217, 54055 / 27557, 949247 / 476920, 3310126 / 1657059,
          2635492 / 1318143, 1580265 / 790192, 1221775 / 610899, 3612247 / 1806132, 849943 / 424972]
#align real.pi_gt_3141592 Real.pi_gt_3141592

theorem pi_lt_3141593 : π < 3.141593 := by
    pi_upper_bound
        [27720 / 19601, 56935 / 30813, 49359 / 25163, 258754 / 130003, 113599 / 56868,
          1101994 / 551163, 8671537 / 4336095, 3877807 / 1938940, 52483813 / 26242030,
          56946167 / 28473117, 23798415 / 11899211]
#align real.pi_lt_3141593 Real.pi_lt_3141593

end Real

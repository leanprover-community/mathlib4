/-
Copyright (c) 2021 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, David Renshaw
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

example : (2 : ℝ) ^ (3 : ℝ) = 8 := by norm_num1
example : (1 : ℝ) ^ (20 : ℝ) = 1 := by norm_num1
example : (-2 : ℝ) ^ (3 : ℝ) = -8 := by norm_num1
example : (1/5 : ℝ) ^ (2 : ℝ) = 1/25 := by norm_num1
example : (-1/3 : ℝ) ^ (-3 : ℝ) = -27 := by norm_num1
example : (1/2 : ℝ) ^ (-3 : ℝ) = 8 := by norm_num1
example : (2 : ℝ) ^ (-3 : ℝ) = 1/8 := by norm_num1
example : (-2 : ℝ) ^ (-3 : ℝ) = -1/8 := by norm_num1

example : (8 : ℝ) ^ (2 / 6 : ℝ) = 2 := by norm_num1
example : (0 : ℝ) ^ (1 / 3 : ℝ) = 0 := by norm_num1
example : (8 / 27 : ℝ) ^ (1 / 3 : ℝ) = 2 / 3 := by norm_num1
example : (8 : ℝ) ^ (-1 / 3 : ℝ) = 1 / 2 := by norm_num1
example : (8 / 27 : ℝ) ^ (-1 / 3 : ℝ) = 3 / 2 := by norm_num1
example : (1 / 27 : ℝ) ^ (-1 / 3 : ℝ) = 3 := by norm_num1

example : (0 : ℝ) ^ (0 : ℝ) = 1 := by norm_num1
example : (0 : ℝ) ^ (1 / 3 : ℝ) = 0 := by norm_num1
example : (0 : ℝ) ^ (-1 / 3 : ℝ) = 0 := by norm_num1

-- The following example is incorrect with the current Mathlib definition.
/--
error: unsolved goals
⊢ (-8) ^ (1 / 3) = -2
-/
#guard_msgs in
example : (-8 : ℝ) ^ (1 / 3 : ℝ) = -2 := by
  norm_num1

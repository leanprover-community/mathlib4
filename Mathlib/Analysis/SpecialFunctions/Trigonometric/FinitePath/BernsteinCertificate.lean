/-
Copyright (c) 2026 Eduardo Nava-Hernandez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Nava-Hernandez
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.FinitePath.Coherence

/-!
# Polynomial certificate for the finite path coherence derivative

A rational polynomial is negative on the rectangle used to bound the coherence derivative.
-/

@[expose] public section

namespace Real.FinitePath

set_option maxHeartbeats 4000000 in
-- The polynomial normalization in this proof exceeds the default heartbeat budget.
set_option maxRecDepth 4000 in
theorem coherence_derivative_remainder_neg {y p : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 5)
    (hp0 : 3 ≤ p) (hp1 : p ≤ 22 / 7) :
    (5 * p ^ 12 * y ^ 12 - 180 * p ^ 10 * y ^ 10 +
      1880 * p ^ 8 * y ^ 8 - 160 * p ^ 8 * y ^ 6 +
      160 * p ^ 8 * y ^ 5 - 7552 * p ^ 6 * y ^ 6 -
      384 * p ^ 6 * y ^ 5 + 2048 * p ^ 6 * y ^ 4 -
      2144 * p ^ 6 * y ^ 3 + 6720 * p ^ 4 * y ^ 4 +
      7680 * p ^ 4 * y ^ 3 - 5760 * p ^ 4 * y ^ 2 +
      7680 * p ^ 4 * y + 34560 * p ^ 2 * y ^ 2 -
      46080 * p ^ 2 * y - 11520 * p ^ 2 + 69120) / 5760 < 0 := by
  let u : ℝ := 5 * y
  let v : ℝ := 7 * p - 21
  have hu0 : 0 ≤ u := by dsimp [u]; positivity
  have hu1 : 0 ≤ 1 - u := by dsimp [u]; norm_num at hy1 ⊢; linarith
  have hv0 : 0 ≤ v := by dsimp [v]; linarith
  have hv1 : 0 ≤ 1 - v := by dsimp [v]; norm_num at hp1 ⊢; linarith
  have hb_0_0 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_0_1 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_0_2 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_0_3 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_0_4 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_0_5 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_0_6 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_0_7 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_0_8 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_0_9 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_0_10 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_0_11 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_0_12 : 0 ≤ u ^ 0 * (1 - u) ^ 12 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_1_0 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_1_1 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_1_2 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_1_3 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_1_4 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_1_5 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_1_6 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_1_7 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_1_8 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_1_9 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_1_10 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_1_11 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_1_12 : 0 ≤ u ^ 1 * (1 - u) ^ 11 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_2_0 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_2_1 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_2_2 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_2_3 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_2_4 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_2_5 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_2_6 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_2_7 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_2_8 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_2_9 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_2_10 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_2_11 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_2_12 : 0 ≤ u ^ 2 * (1 - u) ^ 10 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_3_0 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_3_1 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_3_2 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_3_3 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_3_4 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_3_5 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_3_6 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_3_7 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_3_8 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_3_9 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_3_10 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_3_11 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_3_12 : 0 ≤ u ^ 3 * (1 - u) ^ 9 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_4_0 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_4_1 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_4_2 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_4_3 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_4_4 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_4_5 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_4_6 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_4_7 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_4_8 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_4_9 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_4_10 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_4_11 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_4_12 : 0 ≤ u ^ 4 * (1 - u) ^ 8 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_5_0 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_5_1 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_5_2 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_5_3 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_5_4 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_5_5 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_5_6 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_5_7 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_5_8 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_5_9 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_5_10 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_5_11 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_5_12 : 0 ≤ u ^ 5 * (1 - u) ^ 7 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_6_0 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_6_1 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_6_2 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_6_3 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_6_4 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_6_5 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_6_6 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_6_7 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_6_8 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_6_9 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_6_10 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_6_11 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_6_12 : 0 ≤ u ^ 6 * (1 - u) ^ 6 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_7_0 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_7_1 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_7_2 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_7_3 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_7_4 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_7_5 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_7_6 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_7_7 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_7_8 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_7_9 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_7_10 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_7_11 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_7_12 : 0 ≤ u ^ 7 * (1 - u) ^ 5 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_8_0 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_8_1 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_8_2 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_8_3 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_8_4 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_8_5 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_8_6 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_8_7 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_8_8 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_8_9 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_8_10 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_8_11 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_8_12 : 0 ≤ u ^ 8 * (1 - u) ^ 4 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_9_0 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_9_1 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_9_2 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_9_3 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_9_4 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_9_5 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_9_6 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_9_7 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_9_8 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_9_9 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_9_10 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_9_11 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_9_12 : 0 ≤ u ^ 9 * (1 - u) ^ 3 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_10_0 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_10_1 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_10_2 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_10_3 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_10_4 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_10_5 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_10_6 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_10_7 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_10_8 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_10_9 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_10_10 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_10_11 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_10_12 : 0 ≤ u ^ 10 * (1 - u) ^ 2 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_11_0 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_11_1 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_11_2 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_11_3 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_11_4 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_11_5 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_11_6 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_11_7 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_11_8 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_11_9 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_11_10 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_11_11 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_11_12 : 0 ≤ u ^ 11 * (1 - u) ^ 1 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  have hb_12_0 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 0 * (1 - v) ^ 12) := by positivity
  have hb_12_1 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 1 * (1 - v) ^ 11) := by positivity
  have hb_12_2 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 2 * (1 - v) ^ 10) := by positivity
  have hb_12_3 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 3 * (1 - v) ^ 9) := by positivity
  have hb_12_4 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 4 * (1 - v) ^ 8) := by positivity
  have hb_12_5 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 5 * (1 - v) ^ 7) := by positivity
  have hb_12_6 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 6 * (1 - v) ^ 6) := by positivity
  have hb_12_7 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 7 * (1 - v) ^ 5) := by positivity
  have hb_12_8 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 8 * (1 - v) ^ 4) := by positivity
  have hb_12_9 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 9 * (1 - v) ^ 3) := by positivity
  have hb_12_10 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 10 * (1 - v) ^ 2) := by positivity
  have hb_12_11 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 11 * (1 - v) ^ 1) := by positivity
  have hb_12_12 : 0 ≤ u ^ 12 * (1 - u) ^ 0 * (v ^ 12 * (1 - v) ^ 0) := by positivity
  dsimp [u, v] at hb_0_0 hb_0_1 hb_0_2 hb_0_3 hb_0_4 hb_0_5 hb_0_6 hb_0_7
  dsimp [u, v] at hb_0_8 hb_0_9 hb_0_10 hb_0_11 hb_0_12 hb_1_0 hb_1_1 hb_1_2
  dsimp [u, v] at hb_1_3 hb_1_4 hb_1_5 hb_1_6 hb_1_7 hb_1_8 hb_1_9 hb_1_10
  dsimp [u, v] at hb_1_11 hb_1_12 hb_2_0 hb_2_1 hb_2_2 hb_2_3 hb_2_4 hb_2_5
  dsimp [u, v] at hb_2_6 hb_2_7 hb_2_8 hb_2_9 hb_2_10 hb_2_11 hb_2_12 hb_3_0
  dsimp [u, v] at hb_3_1 hb_3_2 hb_3_3 hb_3_4 hb_3_5 hb_3_6 hb_3_7 hb_3_8
  dsimp [u, v] at hb_3_9 hb_3_10 hb_3_11 hb_3_12 hb_4_0 hb_4_1 hb_4_2 hb_4_3
  dsimp [u, v] at hb_4_4 hb_4_5 hb_4_6 hb_4_7 hb_4_8 hb_4_9 hb_4_10 hb_4_11
  dsimp [u, v] at hb_4_12 hb_5_0 hb_5_1 hb_5_2 hb_5_3 hb_5_4 hb_5_5 hb_5_6
  dsimp [u, v] at hb_5_7 hb_5_8 hb_5_9 hb_5_10 hb_5_11 hb_5_12 hb_6_0 hb_6_1
  dsimp [u, v] at hb_6_2 hb_6_3 hb_6_4 hb_6_5 hb_6_6 hb_6_7 hb_6_8 hb_6_9
  dsimp [u, v] at hb_6_10 hb_6_11 hb_6_12 hb_7_0 hb_7_1 hb_7_2 hb_7_3 hb_7_4
  dsimp [u, v] at hb_7_5 hb_7_6 hb_7_7 hb_7_8 hb_7_9 hb_7_10 hb_7_11 hb_7_12
  dsimp [u, v] at hb_8_0 hb_8_1 hb_8_2 hb_8_3 hb_8_4 hb_8_5 hb_8_6 hb_8_7
  dsimp [u, v] at hb_8_8 hb_8_9 hb_8_10 hb_8_11 hb_8_12 hb_9_0 hb_9_1 hb_9_2
  dsimp [u, v] at hb_9_3 hb_9_4 hb_9_5 hb_9_6 hb_9_7 hb_9_8 hb_9_9 hb_9_10
  dsimp [u, v] at hb_9_11 hb_9_12 hb_10_0 hb_10_1 hb_10_2 hb_10_3 hb_10_4 hb_10_5
  dsimp [u, v] at hb_10_6 hb_10_7 hb_10_8 hb_10_9 hb_10_10 hb_10_11 hb_10_12 hb_11_0
  dsimp [u, v] at hb_11_1 hb_11_2 hb_11_3 hb_11_4 hb_11_5 hb_11_6 hb_11_7 hb_11_8
  dsimp [u, v] at hb_11_9 hb_11_10 hb_11_11 hb_11_12 hb_12_0 hb_12_1 hb_12_2 hb_12_3
  dsimp [u, v] at hb_12_4 hb_12_5 hb_12_6 hb_12_7 hb_12_8 hb_12_9 hb_12_10 hb_12_11
  dsimp [u, v] at hb_12_12
  ring_nf at hb_0_0 hb_0_1 hb_0_2 hb_0_3 hb_0_4 hb_0_5 hb_0_6 hb_0_7
  ring_nf at hb_0_8 hb_0_9 hb_0_10 hb_0_11 hb_0_12 hb_1_0 hb_1_1 hb_1_2
  ring_nf at hb_1_3 hb_1_4 hb_1_5 hb_1_6 hb_1_7 hb_1_8 hb_1_9 hb_1_10
  ring_nf at hb_1_11 hb_1_12 hb_2_0 hb_2_1 hb_2_2 hb_2_3 hb_2_4 hb_2_5
  ring_nf at hb_2_6 hb_2_7 hb_2_8 hb_2_9 hb_2_10 hb_2_11 hb_2_12 hb_3_0
  ring_nf at hb_3_1 hb_3_2 hb_3_3 hb_3_4 hb_3_5 hb_3_6 hb_3_7 hb_3_8
  ring_nf at hb_3_9 hb_3_10 hb_3_11 hb_3_12 hb_4_0 hb_4_1 hb_4_2 hb_4_3
  ring_nf at hb_4_4 hb_4_5 hb_4_6 hb_4_7 hb_4_8 hb_4_9 hb_4_10 hb_4_11
  ring_nf at hb_4_12 hb_5_0 hb_5_1 hb_5_2 hb_5_3 hb_5_4 hb_5_5 hb_5_6
  ring_nf at hb_5_7 hb_5_8 hb_5_9 hb_5_10 hb_5_11 hb_5_12 hb_6_0 hb_6_1
  ring_nf at hb_6_2 hb_6_3 hb_6_4 hb_6_5 hb_6_6 hb_6_7 hb_6_8 hb_6_9
  ring_nf at hb_6_10 hb_6_11 hb_6_12 hb_7_0 hb_7_1 hb_7_2 hb_7_3 hb_7_4
  ring_nf at hb_7_5 hb_7_6 hb_7_7 hb_7_8 hb_7_9 hb_7_10 hb_7_11 hb_7_12
  ring_nf at hb_8_0 hb_8_1 hb_8_2 hb_8_3 hb_8_4 hb_8_5 hb_8_6 hb_8_7
  ring_nf at hb_8_8 hb_8_9 hb_8_10 hb_8_11 hb_8_12 hb_9_0 hb_9_1 hb_9_2
  ring_nf at hb_9_3 hb_9_4 hb_9_5 hb_9_6 hb_9_7 hb_9_8 hb_9_9 hb_9_10
  ring_nf at hb_9_11 hb_9_12 hb_10_0 hb_10_1 hb_10_2 hb_10_3 hb_10_4 hb_10_5
  ring_nf at hb_10_6 hb_10_7 hb_10_8 hb_10_9 hb_10_10 hb_10_11 hb_10_12 hb_11_0
  ring_nf at hb_11_1 hb_11_2 hb_11_3 hb_11_4 hb_11_5 hb_11_6 hb_11_7 hb_11_8
  ring_nf at hb_11_9 hb_11_10 hb_11_11 hb_11_12 hb_12_0 hb_12_1 hb_12_2 hb_12_3
  ring_nf at hb_12_4 hb_12_5 hb_12_6 hb_12_7 hb_12_8 hb_12_9 hb_12_10 hb_12_11
  ring_nf at hb_12_12
  ring_nf
  linarith [hb_0_0, hb_0_1, hb_0_2, hb_0_3, hb_0_4, hb_0_5, hb_0_6, hb_0_7, hb_0_8, hb_0_9,
    hb_0_10, hb_0_11, hb_0_12, hb_1_0, hb_1_1, hb_1_2, hb_1_3, hb_1_4, hb_1_5, hb_1_6, hb_1_7,
    hb_1_8, hb_1_9, hb_1_10, hb_1_11, hb_1_12, hb_2_0, hb_2_1, hb_2_2, hb_2_3, hb_2_4, hb_2_5,
    hb_2_6, hb_2_7, hb_2_8, hb_2_9, hb_2_10, hb_2_11, hb_2_12, hb_3_0, hb_3_1, hb_3_2, hb_3_3,
    hb_3_4, hb_3_5, hb_3_6, hb_3_7, hb_3_8, hb_3_9, hb_3_10, hb_3_11, hb_3_12, hb_4_0, hb_4_1,
    hb_4_2, hb_4_3, hb_4_4, hb_4_5, hb_4_6, hb_4_7, hb_4_8, hb_4_9, hb_4_10, hb_4_11, hb_4_12,
    hb_5_0, hb_5_1, hb_5_2, hb_5_3, hb_5_4, hb_5_5, hb_5_6, hb_5_7, hb_5_8, hb_5_9, hb_5_10,
    hb_5_11, hb_5_12, hb_6_0, hb_6_1, hb_6_2, hb_6_3, hb_6_4, hb_6_5, hb_6_6, hb_6_7, hb_6_8,
    hb_6_9, hb_6_10, hb_6_11, hb_6_12, hb_7_0, hb_7_1, hb_7_2, hb_7_3, hb_7_4, hb_7_5, hb_7_6,
    hb_7_7, hb_7_8, hb_7_9, hb_7_10, hb_7_11, hb_7_12, hb_8_0, hb_8_1, hb_8_2, hb_8_3, hb_8_4,
    hb_8_5, hb_8_6, hb_8_7, hb_8_8, hb_8_9, hb_8_10, hb_8_11, hb_8_12, hb_9_0, hb_9_1, hb_9_2,
    hb_9_3, hb_9_4, hb_9_5, hb_9_6, hb_9_7, hb_9_8, hb_9_9, hb_9_10, hb_9_11, hb_9_12, hb_10_0,
    hb_10_1, hb_10_2, hb_10_3, hb_10_4, hb_10_5, hb_10_6, hb_10_7, hb_10_8, hb_10_9, hb_10_10,
    hb_10_11, hb_10_12, hb_11_0, hb_11_1, hb_11_2, hb_11_3, hb_11_4, hb_11_5, hb_11_6, hb_11_7,
    hb_11_8, hb_11_9, hb_11_10, hb_11_11, hb_11_12, hb_12_0, hb_12_1, hb_12_2, hb_12_3, hb_12_4,
    hb_12_5, hb_12_6, hb_12_7, hb_12_8, hb_12_9, hb_12_10, hb_12_11, hb_12_12]

end Real.FinitePath

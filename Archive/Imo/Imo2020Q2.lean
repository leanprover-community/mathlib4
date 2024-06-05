/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers, Yury Kudryashov
-/
import Mathlib.Analysis.MeanInequalities

#align_import imo.imo2020_q2 from "leanprover-community/mathlib"@"5f25c089cb34db4db112556f23c50d12da81b297"

/-!
# IMO 2020 Q2

The real numbers `a`, `b`, `c`, `d` are such that `a ≥ b ≥ c ≥ d > 0` and `a + b + c + d = 1`.
Prove that `(a + 2b + 3c + 4d) a^a b^b c^c d^d < 1`.

A solution is to eliminate the powers using weighted AM-GM and replace
`1` by `(a+b+c+d)^3`, leaving a homogeneous inequality that can be
proved in many ways by expanding, rearranging and comparing individual
terms.  The version here using factors such as `a+3b+3c+3d` is from
the official solutions.
-/


open Real

theorem imo2020_q2 (a b c d : ℝ) (hd0 : 0 < d) (hdc : d ≤ c) (hcb : c ≤ b) (hba : b ≤ a)
    (h1 : a + b + c + d = 1) : (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d < 1 := by
  have hp : a ^ a * b ^ b * c ^ c * d ^ d ≤ a * a + b * b + c * c + d * d := by
    refine geom_mean_le_arith_mean4_weighted ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h1 <;> linarith
  calc
    (a + 2 * b + 3 * c + 4 * d) * a ^ a * b ^ b * c ^ c * d ^ d =
        (a + 2 * b + 3 * c + 4 * d) * (a ^ a * b ^ b * c ^ c * d ^ d) := by ac_rfl
    _ ≤ (a + 2 * b + 3 * c + 4 * d) * (a * a + b * b + c * c + d * d) := by gcongr; linarith
    _ = (a + 2 * b + 3 * c + 4 * d) * a ^ 2 + (a + 2 * b + 3 * c + 4 * d) * b ^ 2
        + (a + 2 * b + 3 * c + 4 * d) * c ^ 2 + (a + 2 * b + 3 * c + 4 * d) * d ^ 2 := by ring
    _ ≤ (a + 3 * b + 3 * c + 3 * d) * a ^ 2 + (3 * a + b + 3 * c + 3 * d) * b ^ 2
        + (3 * a + 3 * b + c + 3 * d) * c ^ 2 + (3 * a + 3 * b + 3 * c + d) * d ^ 2 := by
        gcongr ?_ * _ + ?_ * _ + ?_ * _ + ?_ * _ <;> linarith
    _ < (a + 3 * b + 3 * c + 3 * d) * a ^ 2 + (3 * a + b + 3 * c + 3 * d) * b ^ 2
        + (3 * a + 3 * b + c + 3 * d) * c ^ 2 + (3 * a + 3 * b + 3 * c + d) * d ^ 2
        + (6 * a * b * c + 6 * a * b * d + 6 * a * c * d + 6 * b * c * d) :=
        (lt_add_of_pos_right _ (by apply_rules [add_pos, mul_pos, zero_lt_one] <;> linarith))
    _ = (a + b + c + d) ^ 3 := by ring
    _ = 1 := by simp [h1]
#align imo2020_q2 imo2020_q2

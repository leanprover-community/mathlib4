/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.ModRw

-- attribute [irreducible] Int.mod Int.ModEq
-- local attribute [-norm_num] NormNum.eval_nat_int_ext

-- set_option trace.aesop.steps true

example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] := by
  mod_rw
  -- mod_rw [ha]

example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : 3 ≡ b [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  mod_rw
  -- mod_rw [ha, hb]

example {x : ℤ} (hx : x ≡ 0 [ZMOD 3]): x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by
  mod_rw
  -- mod_rw hx

example {x : ℤ} (hx : x ≡ 2 [ZMOD 3]): x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by
  mod_rw
  -- mod_rw hx

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by
  mod_rw

example {n : ℤ} (hn : n ≡ 1 [ZMOD 2]) :
    5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by
  mod_rw

example {x : ℤ} (hx : x ≡ 3 [ZMOD 5] ): x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by
  mod_rw

/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.RelCongr.ModEq

-- attribute [irreducible] Int.mod Int.ModEq
-- local attribute [-norm_num] NormNum.eval_nat_int_ext


example (ha : a ≡ 2 [ZMOD 4]) : a * b ^ 2 + a ^ 2 * b + 3 ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] := by
  rel_congr

example (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  rel_congr

-- FIXME in `assumption` tactic, also try `symmetry ; assumption`
example (hb : 3 ≡ b [ZMOD 5]) : b ^ 2 ≡ 3 ^ 2 [ZMOD 5] := by rel_congr

example (hx : x ≡ 0 [ZMOD 3]): x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by rel_congr

example (hx : x ≡ 2 [ZMOD 3]): x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by rel_congr

example (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by rel_congr

example (hn : n ≡ 1 [ZMOD 2]) : 5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by
  rel_congr

example (hx : x ≡ 3 [ZMOD 5] ): x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by rel_congr

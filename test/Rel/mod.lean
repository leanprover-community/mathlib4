/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Tactic.Rel

example {a b : ℤ} (ha : a ≡ 2 [ZMOD 4]) :
    a * b ^ 2 + a ^ 2 * b + 3 ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] := by
  rel [ha]

example {a b : ℤ} (ha : a ≡ 4 [ZMOD 5]) (hb : 3 ≡ b [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  rel [ha, hb.symm]

example {x : ℤ} (hx : x ≡ 0 [ZMOD 3]) : x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by
  rel [hx]

example {x : ℤ} (hx : x ≡ 2 [ZMOD 3]) : x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by
  rel [hx]

example {n : ℤ} (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by
  rel [hn]

example {n : ℤ} (hn : n ≡ 1 [ZMOD 2]) :
    5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by
  rel [hn]

example {x : ℤ} (hx : x ≡ 3 [ZMOD 5] ): x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by
  rel [hx]

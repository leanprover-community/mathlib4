/-
Copyright (c) 2022 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Data.Int.ModEq

/-! # Modular arithmetic tests for the `gcongr` tactic -/

variable {a b n x : ℤ}

example (ha : a ≡ 2 [ZMOD 4]) : a * b ^ 2 + a ^ 2 * b + 3 ≡ 2 * b ^ 2 + 2 ^ 2 * b + 3 [ZMOD 4] := by
  gcongr

example (ha : a ≡ 4 [ZMOD 5]) (hb : b ≡ 3 [ZMOD 5]) :
    a * b + b ^ 3 + 3 ≡ 4 * 3 + 3 ^ 3 + 3 [ZMOD 5] := by
  gcongr

example (hb : 3 ≡ b [ZMOD 5]) : b ^ 2 ≡ 3 ^ 2 [ZMOD 5] := by gcongr
example (hb : 3 ≡ b [ZMOD 5]) : b ^ 2 ≡ 3 ^ 2 [ZMOD 5] := by gcongr ?_ ^ 2
example (hb : 3 ≡ b [ZMOD 5]) : b ^ 2 ≡ 3 ^ 2 [ZMOD 5] := by rel [hb]

example (hx : x ≡ 0 [ZMOD 3]) : x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by gcongr
example (hx : x ≡ 0 [ZMOD 3]) : x ^ 3 ≡ 0 ^ 3 [ZMOD 3] := by gcongr ?_ ^ 3

example (hx : x ≡ 2 [ZMOD 3]) : x ^ 3 ≡ 2 ^ 3 [ZMOD 3] := by gcongr

example (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by gcongr
example (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by gcongr ?_ ^ 3 + 7 * ?_
example (hn : n ≡ 1 [ZMOD 3]) : n ^ 3 + 7 * n ≡ 1 ^ 3 + 7 * 1 [ZMOD 3] := by rel [hn]

example (hn : n ≡ 1 [ZMOD 2]) : 5 * n ^ 2 + 3 * n + 7 ≡ 5 * 1 ^ 2 + 3 * 1 + 7 [ZMOD 2] := by
  gcongr

example (hx : x ≡ 3 [ZMOD 5]) : x ^ 5 ≡ 3 ^ 5 [ZMOD 5] := by gcongr

/-! Test that `gcongr` can deal with `_ ≡ _ [ZMOD _] → _ ≡ _ [ZMOD _]` -/
variable {a b : ℤ}

example (h1 : 0 ≡ a [ZMOD 7]) (h2 : 0 ≡ b [ZMOD 7]) : b ≡ a + 1 [ZMOD 7] → 0 ≡ 0 + 1 [ZMOD 7] := by
  gcongr
example (h1 : 0 ≡ a [ZMOD 7]) (_h2 : 0 ≡ b [ZMOD 7]) : b ≡ a + 1 [ZMOD 7] → b ≡ 0 + 1 [ZMOD 7] := by
  gcongr
example (_h1 : 0 ≡ a [ZMOD 7]) (h2 : 0 ≡ b [ZMOD 7]) : b ≡ a + 1 [ZMOD 7] → 0 ≡ a + 1 [ZMOD 7] := by
  gcongr

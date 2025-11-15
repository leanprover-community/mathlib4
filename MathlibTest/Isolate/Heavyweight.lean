/-
Copyright (c) 2025 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Isolate

open Real

private axiom test_sorry : ∀ {α}, α

example {x : ℝ} (hx : 0 < x) : log (2 + 3 * x) < 11 := by
  isolate x
  guard_target = x < (rexp 11 - 2) / 3
  exact test_sorry

example {x : ℝ} : log (√x) > 11 := by
  isolate x
  guard_target = (exp 11) ^ 2 < x
  exact test_sorry
  guard_target = 0 < √x
  exact test_sorry

example {x : ℝ} : log (exp (x - 3) + 2) < 11 := by
  isolate x - 3
  guard_target = x - 3 < log (exp 11 - 2)
  exact test_sorry
  guard_target = 0 < exp 11 - 2
  exact test_sorry

example {t : ℝ} (ht : 10 ≤ t) : (√t - 3) ^ (3:ℝ) = 1 := by
  isolate t
  · norm_num
    guard_target = t = 16
    exact test_sorry
  isolate t
  norm_num
  guard_target = 9 ≤ t
  linear_combination ht

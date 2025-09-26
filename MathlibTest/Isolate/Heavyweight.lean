import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Isolate.Tagging

open Real

private axiom test_sorry : ∀ {α}, α

example {x : ℝ} : log (2 + 3 * x) < 11 := by
  isolate x
  guard_target = x < (rexp 11 - 2) / 3
  exact test_sorry
  guard_target = 0 < 2 + 3 * x
  exact test_sorry

example {x : ℝ} : log (√x) > 11 := by
  isolate x
  guard_target = (exp 11) ^ 2 < x
  exact test_sorry
  guard_target = 0 < √x
  exact test_sorry

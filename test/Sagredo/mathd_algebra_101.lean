-- from miniF2F https://github.com/facebookresearch
import Mathlib.Tactic.GPT.Sagredo.Dialog
import Mathlib.Data.Real.Basic

open Real

theorem mathd_algebra_101 (x : ℝ) (h₀ : x^2 - 5 * x - 4 ≤ 10) :
  x ≥ -2 ∧ x ≤ 7 := by
  sagredo

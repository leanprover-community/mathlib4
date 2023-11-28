import Mathlib.Tactic.ByApprox
import Mathlib.Tactic.ByApprox.Lemmas

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential

set_option trace.ByApprox true
-- set_option trace.profiler true

open Real

example : (3 : ℝ)/5 < 3/4 := by by_approx

example : (123435890871235 : ℝ) ≥ 32587987398 := by by_approx

example : sqrt 2 < 1.41423 := by by_approx

example : sqrt (sqrt 10) ≥ 1.7 := by by_approx

example : sqrt 2 + sqrt 3 < 3.2 := by by_approx

example : sqrt (sqrt 3 - sqrt 2) > 1/2 := by by_approx

example : - sqrt 2 < -1 := by by_approx

example : sqrt (sqrt 10 - sqrt 9) < 1/2 := by by_approx

example : (sqrt 2)⁻¹ > 0.7 := by by_approx

example : (-sqrt 5)⁻¹ > -1 := by by_approx

example : (-sqrt 5)⁻¹ < -1/5 := by by_approx

example : sqrt 2 * sqrt 3 ≠ 2 := by by_approx

example : sqrt 2 * sqrt 3 ≠ 100 := by by_approx

example : 10 / sqrt 11 < sqrt 10 := by by_approx

example : Real.exp 2 > 7 := by by_approx

open BigOperators Finset

set_option trace.Tactic.norm_num true
example : (10).factorial > 5 := by
  -- conv =>
  --   lhs
  --   whnf
  norm_num


  sorry

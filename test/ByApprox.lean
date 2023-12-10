import Mathlib.Tactic.ByApprox
import Mathlib.Tactic.ByApprox.Lemmas

import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Complex.Exponential

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

example : exp 1 > 2.7182818 := by by_approx

example : exp 1 < 2.7182819 := by by_approx

example : exp (sqrt 10) < 23.6244 := by by_approx

example : exp (sqrt 10) > 23.6243 := by by_approx

example : exp (- sqrt 2) < 0.25 := by by_approx

example : exp (- sqrt 2) > 0.24 := by by_approx

example : |sqrt 2 - 1.414| < 0.001 := by by_approx

example : |sqrt 10| > 3 := by by_approx

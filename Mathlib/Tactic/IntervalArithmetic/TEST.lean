module

public meta import Mathlib.Tactic.IntervalArithmetic.RatReal

set_option linter.style.header false

#time example :
    (7.3890560989306502 : ℝ) ≤ Real.exp (2 : ℝ) ∧
    Real.exp (2 : ℝ) ≤ (7.3890560989306503 : ℝ) := by
  constructor <;> interval RatReal 9

example :
    (7.38905609893065022723042746057500781318031557055184732408712782252257379607905705790229082941064210 : ℝ)
      ≤ Real.exp (2 : ℝ) ∧
    Real.exp (2 : ℝ)
      ≤ (7.38905609893065022723042746057500781318031557055184732408712782252257379607905705790229082941064211 : ℝ) := by
  constructor <;> interval RatReal 500

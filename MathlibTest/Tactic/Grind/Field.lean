import Mathlib

example (x y : ℝ) (h : x ≠ y) : (x^2 - y^2)/(x - y) = x + y := by grind
example (x y : ℝ) (h : (x + y)^2 ≠ 0) : (x^2 - y^2)/(x + y) = x - y := by grind

import Mathlib
import Mathlib.Tactic.Polynomial



set_option profiler true


/-
share common exprs took 104ms
type checking took 306ms

-/
example (a : ℚ) : (.C a + Polynomial.X)^(1+7/3)
  = .X ^ 3 + .C (3 * a) * .X^2  + .C (3 * a^2) * .X  + .C (a^3) := by
  poly
  congr <;> ring

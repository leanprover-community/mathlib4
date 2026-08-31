module

public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.Algebra.Rat

set_option linter.style.header false

variable (a b : ℚ) [Fact (∀ r, r ^ 2 ≠ a + b * r)]

example : @DivisionRing.toRatAlgebra (QuadraticAlgebra ℚ a b) _ _ =
    QuadraticAlgebra.instAlgebra := by
  with_implicit rfl

example : @DivisionRing.toRatAlgebra (QuadraticAlgebra ℚ a b) _ _ =
    QuadraticAlgebra.instAlgebra := rfl   

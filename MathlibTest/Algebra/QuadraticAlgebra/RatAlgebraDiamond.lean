module

import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.QuadraticAlgebra.Basic

variable (a b : ℚ) [Fact (∀ r, r ^ 2 ≠ a + b * r)]

example : @Eq (Algebra ℚ (QuadraticAlgebra ℚ a b))
    DivisionRing.toRatAlgebra QuadraticAlgebra.instAlgebra := by
  rfl

/--
error: Tactic `rfl` failed: The left-hand side
  DivisionRing.toRatAlgebra
is not definitionally equal to the right-hand side
  QuadraticAlgebra.instAlgebra

a b : ℚ
inst✝ : Fact (∀ (r : ℚ), r ^ 2 ≠ a + b * r)
⊢ DivisionRing.toRatAlgebra = QuadraticAlgebra.instAlgebra
-/
#guard_msgs in
example : @Eq (Algebra ℚ (QuadraticAlgebra ℚ a b))
    DivisionRing.toRatAlgebra QuadraticAlgebra.instAlgebra := by
  with_reducible_and_instances rfl

import Mathlib

import Mathlib.Tactic.Algebra


section Polynomial
open Polynomial

example (x y z : ℚ) :
    (X + 2) * (X + C x) = X * X + C (2 + x) * X + C (2 * x) := by
  simp_rw [← Polynomial.algebraMap_eq, Algebra.algebraMap_eq_smul_one]
  algebra ℚ (Polynomial ℚ)


end Polynomial

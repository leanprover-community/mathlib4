import Mathlib.Tactic.Simproc.PolynomialDegree
import Mathlib.Data.Polynomial.Basic

variable {R : Type*} [Semiring R]

example : Polynomial.natDegree (Polynomial.X : R[X]) = 1 := by simp

example : Polynomial.natDegree (Polynomial.C (1 : R)) = 0 := by simp

example : Polynomial.degree (Polynomial.X : R[X]) = (1 : WithBot ℕ) := by simp

section ExplicitPolynomials

#check (Polynomial.X : R[X])
#check (Polynomial.C (1 : R))
#check (Polynomial.X + Polynomial.C (1 : R) : R[X])
#check (Polynomial.X * Polynomial.X : R[X])

end ExplicitPolynomials

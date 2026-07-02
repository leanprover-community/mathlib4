module
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.RingTheory.MvPolynomial


/-! # The `polynomial` tactic -/

axiom sorryPolynomialTest {P : Prop} : P

section poly
open Polynomial

example (a : ℚ) : (X + C a)^2 = X^2 + C (2*a) * X +  C (a^2) := by
  polynomial

example (a : ℚ) : (X + C a)^2 = X^2 + (2*a) • X +  C (a^2) := by
  polynomial

example (a : ℚ) : (2*X + C a)^2 = 4 * monomial 2 1 + monomial 1 (4*a) + monomial 0 (a^2) := by
  polynomial

example (a : ℚ) : (X - C a)*(X + C a) = X^2 - C (a^2) := by
  polynomial

example (a : ℚ) : (C a * X + C 4)^2 = 0 := by
  polynomial_nf
  guard_target = C 16 + C (a * 8) * X + C (a ^ 2) * X ^ 2 = 0
  apply sorryPolynomialTest

example (a b c : ℚ) : (X + C a)^2 = X^2 + C c * X + C b := by
  polynomial_nf
  guard_target = C (a ^ 2) + C (a * 2) * X + X ^ 2 = C b + C c * X + X ^ 2
  apply sorryPolynomialTest

example (a : ℚ) (n : ℕ) : (X^n + C a)^2 = 0 := by
  polynomial_nf
  guard_target = C (a ^ 2) + C (a * 2) * X ^ n + X ^ (n * 2) = 0
  apply sorryPolynomialTest

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {r₁ : R} {a₁ : A} in
example : Polynomial.map (algebraMap R A) (C r₁ * X) = C a₁ * X := by
  polynomial_nf
  guard_target = C ((algebraMap R A) r₁) * X = C a₁ * X
  apply sorryPolynomialTest

example {P : ℚ[X] → Prop} (h : P (X ^ 2 + X + C 4⁻¹)) : P ((X + C 2⁻¹) ^ 2) := by
  polynomial_nf at h ⊢
  exact h

end poly

section mvpoly
open MvPolynomial

example (a : ℚ) : (X 0 + C a)^2 = X 0^2 + C (2*a) * X 0 +  C (a^2) := by
  polynomial

example (a : ℚ) : (X 0 + C a)^2 = X 0^2 + (2*a) • X 0 +  C (a^2) := by
  polynomial

example (a : ℚ) : (X 0 - C a)*(X 0 + C a) = (X 0)^2 - C (a^2) := by
  polynomial

example (a : ℚ) : (X 0 - X 1 * C a)*(X 0 + X 1 * C a) = (X 0)^2 - (X 1) ^ 2 * C (a^2) := by
  polynomial

example (a : ℚ) : ((X 0 + C a)^2).eval (fun _ ↦ -a) = 0 := by
  polynomial_nf
  guard_target = (eval fun i => -a) (C (a ^ 2) + C (a * 2) * X 0 + X 0 ^ 2) = 0
  apply sorryPolynomialTest

example (a b c : ℤ) : (X 0 * C a + X 1 * X 37 * C (b*(c-1)))^2 * (X 0 - 1) = 0 := by
  polynomial_nf
  guard_target = C (a * b * 2 - a * b * c * 2) * (X 0 * X 1 * X 37) +
            C (b ^ 2 - b ^ 2 * c * 2 + b ^ 2 * c ^ 2) * (X 0 * X 1 ^ 2 * X 37 ^ 2) +
          C (-a ^ 2) * X 0 ^ 2 +
        C (-(a * b * 2) + a * b * c * 2) * (X 0 ^ 2 * X 1 * X 37) +
      C (a ^ 2) * X 0 ^ 3 +
    C (-b ^ 2 + (b ^ 2 * c * 2 - b ^ 2 * c ^ 2)) * (X 1 ^ 2 * X 37 ^ 2) = 0
  apply sorryPolynomialTest

end mvpoly

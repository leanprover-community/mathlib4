import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Module.ULift
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Polynomial

section native_decide

open Polynomial

def p0 : ℕ[X] :=
  ⟨⟨{}, Pi.single 0 0, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr p0 = "0" := by native_decide
example : reprStr (Option.some p0) = "some 0" := by native_decide
example : (reprPrec p0 65).pretty = "0" := by native_decide

def pX : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 1, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr pX = "X" := by native_decide
example : reprStr (Option.some pX) = "some X" := by native_decide

def pXsq : ℕ[X] :=
  ⟨⟨{2}, Pi.single 2 1, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr pXsq = "X ^ 2" := by native_decide
example : reprStr (Option.some pXsq) = "some (X ^ 2)" := by native_decide
example : (reprPrec pXsq 65).pretty = "X ^ 2" := by native_decide
example : (reprPrec pXsq 70).pretty = "X ^ 2" := by native_decide
example : (reprPrec pXsq 80).pretty = "(X ^ 2)" := by native_decide

def p1 : ℕ[X] :=
  ⟨⟨{1}, Pi.single 1 37, by intro; simp [Pi.single, Function.update_apply]⟩⟩
example : reprStr p1 = "C 37 * X" := by native_decide
example : reprStr (Option.some p1) = "some (C 37 * X)" := by native_decide
example : (reprPrec p1 65).pretty = "C 37 * X" := by native_decide
example : (reprPrec p1 70).pretty = "(C 37 * X)" := by native_decide

def p2 : ℕ[X] :=
  ⟨⟨{0, 2}, Pi.single 0 57 + Pi.single 2 22,
    by intro; simp [Pi.single, Function.update_apply]; tauto⟩⟩
example : reprStr p2 = "C 57 + C 22 * X ^ 2" := by native_decide
example : (reprPrec p2 65).pretty = "(C 57 + C 22 * X ^ 2)" := by native_decide

-- test that parens are added inside `C`
def pu1 : (ULift.{1} ℕ)[X] :=
  ⟨⟨{1}, Pi.single 1 (ULift.up 37),
    by intro; simp [Pi.single, Function.update_apply, ←ULift.down_inj]⟩⟩
example : reprStr pu1 = "C (ULift.up 37) * X" := by native_decide

end native_decide

/-! # The `polynomial Tactic -/

axiom sorryPolynomialTest {P : Prop} : P
section poly
open _root_.Polynomial

example (a : ℚ) : (X + C a)^2 = X^2 + C (2*a) * X +  C (a^2) := by
  polynomial

example (a : ℚ) : (X + C a)^2 = X^2 + (2*a) • X +  C (a^2) := by
  polynomial

example (a : ℚ) : (2*X + C a)^2 = 4 * monomial 2 1 + monomial 1 (4*a) + monomial 0 (a^2) := by
  polynomial

example (a : ℚ) : (X - C a)*(X + C a) = X^2 - C (a^2) := by
  polynomial

example (a b c : ℚ) : (X + C a)^2 = X^2 + C c * X + C b := by
  match_coefficients
  · guard_target = a^2 = b
    apply sorryPolynomialTest
  · guard_target = a * 2 = c
    apply sorryPolynomialTest


example (a : ℚ) : (X * C (C a) - C X) * (X * C (C a) + C X) = X^2 * (C <| C (a^2)) - C (X^2):= by
  match_coefficients
  -- TODO: The goal here is in terms of `smul` instead of `C`, so we shouldn't just use the `ring` cleanup routine.

example (a b c : ℚ) : (X + C a)^2 = X^2 + C c * X + C b := by
  polynomial_nf
  guard_target = C (a ^ 2) + C (a * 2) * X + X ^ 2 = C b + C c * X + X ^ 2
  apply sorryPolynomialTest


example (a : ℚ) (n : ℕ) : (X^n + C a)^2 = 0 := by
  polynomial_nf
  guard_target = C (a ^ 2) + C (a * 2) * X ^ n + X ^ (n * 2) = 0
  apply sorryPolynomialTest

example (a b c d e : ℚ) (n : ℕ): (X^n + C a)*(X^n + X * C a) =
    X^(2*n) + X^(n+1) * C b + X^n * C c + C d * X + C e := by
  match_coefficients
  · guard_target = e = 0
    apply sorryPolynomialTest
  · guard_target = a^2 = d
    apply sorryPolynomialTest
  · guard_target = a = b
    apply sorryPolynomialTest
  · guard_target = a = c
    apply sorryPolynomialTest

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A] {r₁ r₂ r₃ : R} {a₁ a₂ a₃ : A}
example : Polynomial.map (algebraMap R A) (C r₁ * X) = C a₁ * X := by
  polynomial_nf
  -- simp_rw [Polynomial.map_C]
  match_coefficients
  apply sorryPolynomialTest

end poly

section mvpoly
open _root_.MvPolynomial

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

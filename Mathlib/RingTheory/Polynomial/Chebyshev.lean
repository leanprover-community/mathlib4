/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth
-/
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

#align_import ring_theory.polynomial.chebyshev from "leanprover-community/mathlib"@"d774451114d6045faeb6751c396bea1eb9058946"

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

## Main definitions

* `Polynomial.Chebyshev.T`: the Chebyshev polynomials of the first kind.
* `Polynomial.Chebyshev.U`: the Chebyshev polynomials of the second kind.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `Polynomial.Chebyshev.mul_T`, the product of the `m`-th and `(m + k)`-th Chebyshev polynomials of
  the first kind is the sum of the `(2 * m + k)`-th and `k`-th Chebyshev polynomials of the first
  kind.
* `Polynomial.Chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (Int.castRingHom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `LinearRecurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
-/


noncomputable section

namespace Polynomial.Chebyshev
set_option linter.uppercaseLean3 false -- `T` `U` `X`

open Polynomial

open Polynomial

variable (R S : Type*) [CommRing R] [CommRing S]

/-- `T n` is the `n`-th Chebyshev polynomial of the first kind -/
noncomputable def T : ℕ → R[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * T (n + 1) - T n
#align polynomial.chebyshev.T Polynomial.Chebyshev.T

@[simp]
theorem T_zero : T R 0 = 1 := rfl
#align polynomial.chebyshev.T_zero Polynomial.Chebyshev.T_zero

@[simp]
theorem T_one : T R 1 = X := rfl
#align polynomial.chebyshev.T_one Polynomial.Chebyshev.T_one

@[simp]
theorem T_add_two (n : ℕ) : T R (n + 2) = 2 * X * T R (n + 1) - T R n := by rw [T]
#align polynomial.chebyshev.T_add_two Polynomial.Chebyshev.T_add_two

theorem T_two : T R 2 = 2 * X ^ 2 - 1 := by simp only [T, sub_left_inj, sq, mul_assoc]
#align polynomial.chebyshev.T_two Polynomial.Chebyshev.T_two

theorem T_of_two_le (n : ℕ) (h : 2 ≤ n) : T R n = 2 * X * T R (n - 1) - T R (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact T_add_two R n
#align polynomial.chebyshev.T_of_two_le Polynomial.Chebyshev.T_of_two_le

/-- `U n` is the `n`-th Chebyshev polynomial of the second kind -/
noncomputable def U : ℕ → R[X]
  | 0 => 1
  | 1 => 2 * X
  | n + 2 => 2 * X * U (n + 1) - U n
#align polynomial.chebyshev.U Polynomial.Chebyshev.U

@[simp]
theorem U_zero : U R 0 = 1 := rfl
#align polynomial.chebyshev.U_zero Polynomial.Chebyshev.U_zero

@[simp]
theorem U_one : U R 1 = 2 * X := rfl
#align polynomial.chebyshev.U_one Polynomial.Chebyshev.U_one

@[simp]
theorem U_add_two (n : ℕ) : U R (n + 2) = 2 * X * U R (n + 1) - U R n := by rw [U]
#align polynomial.chebyshev.U_add_two Polynomial.Chebyshev.U_add_two

theorem U_two : U R 2 = 4 * X ^ 2 - 1 := by
  simp only [U]
  ring
#align polynomial.chebyshev.U_two Polynomial.Chebyshev.U_two

theorem U_of_two_le (n : ℕ) (h : 2 ≤ n) : U R n = 2 * X * U R (n - 1) - U R (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact U_add_two R n
#align polynomial.chebyshev.U_of_two_le Polynomial.Chebyshev.U_of_two_le

theorem U_eq_X_mul_U_add_T : ∀ n : ℕ, U R (n + 1) = X * U R n + T R (n + 1)
  | 0 => by simp only [T, U, two_mul, mul_one]
  | 1 => by simp only [T, U]; ring
  | n + 2 => by
    have H₁ := U_eq_X_mul_U_add_T (n + 1)
    have H₂ := U_eq_X_mul_U_add_T n
    have h₁ := U_add_two R (n + 1)
    have h₂ := U_add_two R n
    have h₃ := T_add_two R (n + 1)
    linear_combination -h₃ - (X:R[X]) * h₂ + h₁ + 2 * (X:R[X]) * H₁ - H₂
#align polynomial.chebyshev.U_eq_X_mul_U_add_T Polynomial.Chebyshev.U_eq_X_mul_U_add_T

theorem T_eq_U_sub_X_mul_U (n : ℕ) : T R (n + 1) = U R (n + 1) - X * U R n := by
  linear_combination - U_eq_X_mul_U_add_T R n
#align polynomial.chebyshev.T_eq_U_sub_X_mul_U Polynomial.Chebyshev.T_eq_U_sub_X_mul_U

theorem T_eq_X_mul_T_sub_pol_U : ∀ n : ℕ, T R (n + 2) = X * T R (n + 1) - (1 - X ^ 2) * U R n
  | 0 => by simp only [T, U]; ring
  | 1 => by simp only [T, U]; ring
  | n + 2 => by
    have H₁ := T_eq_X_mul_T_sub_pol_U (n + 1)
    have H₂ := T_eq_X_mul_T_sub_pol_U n
    have h₁ := T_add_two R (n + 1)
    have h₂ := T_add_two R (n + 2)
    have h₃ := U_add_two R n
    linear_combination (-(X:R[X]) ^ 2 + 1) * h₃ + h₂ - (X:R[X]) * h₁ - H₂ + 2 * (X:R[X]) * H₁
#align polynomial.chebyshev.T_eq_X_mul_T_sub_pol_U Polynomial.Chebyshev.T_eq_X_mul_T_sub_pol_U

theorem one_sub_X_sq_mul_U_eq_pol_in_T (n : ℕ) :
    (1 - X ^ 2) * U R n = X * T R (n + 1) - T R (n + 2) := by
  linear_combination T_eq_X_mul_T_sub_pol_U R n
#align polynomial.chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T Polynomial.Chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T

variable {R S}

@[simp]
theorem map_T (f : R →+* S) : ∀ n : ℕ, map f (T R n) = T S n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [map_T]
#align polynomial.chebyshev.map_T Polynomial.Chebyshev.map_T

@[simp]
theorem map_U (f : R →+* S) : ∀ n : ℕ, map f (U R n) = U S n
  | 0 => by simp
  | 1 => by simp
  | n + 2 => by simp [map_U]
#align polynomial.chebyshev.map_U Polynomial.Chebyshev.map_U

theorem T_derivative_eq_U : ∀ n : ℕ, derivative (T R (n + 1)) = (n + 1) * U R n
  | 0 => by simp
  | 1 => by
    simp [T_two, U_one, derivative_sub, derivative_one, derivative_mul, derivative_X_pow, add_mul]
  | n + 2 => by
    have h := congr_arg derivative <| T_add_two R (n + 1)
    simp only [derivative_sub, derivative_mul, derivative_mul, derivative_X, derivative_ofNat] at h
    have H₁ := T_derivative_eq_U (n + 1)
    have H₂ := T_derivative_eq_U n
    have H₃ := T_eq_U_sub_X_mul_U R (n + 1)
    have H₄ := U_add_two R n
    push_cast at *
    linear_combination 2 * (X:R[X]) * H₁ + (-n - 1) * H₄ + 2 * H₃ - H₂ + h
#align polynomial.chebyshev.T_derivative_eq_U Polynomial.Chebyshev.T_derivative_eq_U

theorem one_sub_X_sq_mul_derivative_T_eq_poly_in_T (n : ℕ) :
    (1 - X ^ 2) * derivative (T R (n + 1)) = (n + 1 : R[X]) * (T R n - X * T R (n + 1)) := by
  have H₁ := one_sub_X_sq_mul_U_eq_pol_in_T R n
  have H₂ := T_derivative_eq_U (R := R) n
  have h₁ := T_add_two R n
  linear_combination (-n - 1) * h₁ + (-(X:R[X]) ^ 2 + 1) * H₂ + (n + 1) * H₁
#align polynomial.chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T Polynomial.Chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T

theorem add_one_mul_T_eq_poly_in_U (n : ℕ) :
    ((n : R[X]) + 1) * T R (n + 1) = X * U R n - (1 - X ^ 2) * derivative (U R n) := by
  have h₁ := congr_arg derivative <| T_eq_X_mul_T_sub_pol_U R n
  simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
    T_derivative_eq_U, C_eq_natCast] at h₁
  have h₂ := T_eq_U_sub_X_mul_U R n
  push_cast at *
  linear_combination h₁ + (n + 2) * h₂
#align polynomial.chebyshev.add_one_mul_T_eq_poly_in_U Polynomial.Chebyshev.add_one_mul_T_eq_poly_in_U

variable (R)

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_T : ∀ m k, 2 * T R m * T R (m + k) = T R (2 * m + k) + T R k
  | 0, _ => by simp [two_mul, add_mul]
  | 1, _ => by simp [add_comm]
  | m + 2, k => by
    -- state the inductive hypothesis for a few useful indices
    have H₁ := mul_T (m + 1) (k + 1)
    have H₂ := mul_T m (k + 2)
    -- state the `T` recurrence relation for a few useful indices
    have h₁ := T_add_two R m
    have h₂ := T_add_two R (2 * m + k + 2)
    have h₃ := T_add_two R k
    -- clean up the `T` nat indices
    ring_nf at H₁ H₂ h₁ h₂ h₃ ⊢
    -- the desired identity is an appropriate linear combination of H₁, H₂, h₁, h₂, h₃
    linear_combination 2 * T R (2 + m + k) * h₁ + 2 * (X : R[X]) * H₁ - H₂ - h₂ - h₃
#align polynomial.chebyshev.mul_T Polynomial.Chebyshev.mul_T

/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
theorem T_mul : ∀ m n, T R (m * n) = (T R m).comp (T R n)
  | 0, _ => by simp
  | 1, _ => by simp
  | m + 2, n => by
    have H₁ := T_mul (m + 1) n
    have H₂ := T_mul m n
    have H₃ := mul_T R n (m * n)
    have h := congr_arg (comp · (T R n)) <| T_add_two R m
    simp only [sub_comp, mul_comp, ofNat_comp, X_comp] at h
    ring_nf at *
    linear_combination - H₂ - h - H₃ + 2 * T R n * H₁
#align polynomial.chebyshev.T_mul Polynomial.Chebyshev.T_mul

end Polynomial.Chebyshev

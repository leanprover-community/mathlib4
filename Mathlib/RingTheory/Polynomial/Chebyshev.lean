/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Julian Kuelshammer, Heather Macbeth

! This file was ported from Lean 3 source module ring_theory.polynomial.chebyshev
! leanprover-community/mathlib commit d774451114d6045faeb6751c396bea1eb9058946
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-!
# Chebyshev polynomials

The Chebyshev polynomials are two families of polynomials indexed by `ℕ`,
with integral coefficients.

## Main definitions

* `polynomial.chebyshev.T`: the Chebyshev polynomials of the first kind.
* `polynomial.chebyshev.U`: the Chebyshev polynomials of the second kind.

## Main statements

* The formal derivative of the Chebyshev polynomials of the first kind is a scalar multiple of the
  Chebyshev polynomials of the second kind.
* `polynomial.chebyshev.mul_T`, the product of the `m`-th and `(m + k)`-th Chebyshev polynomials of
  the first kind is the sum of the `(2 * m + k)`-th and `k`-th Chebyshev polynomials of the first
  kind.
* `polynomial.chebyshev.T_mul`, the `(m * n)`-th Chebyshev polynomial of the first kind is the
  composition of the `m`-th and `n`-th Chebyshev polynomials of the first kind.

## Implementation details

Since Chebyshev polynomials have interesting behaviour over the complex numbers and modulo `p`,
we define them to have coefficients in an arbitrary commutative ring, even though
technically `ℤ` would suffice.
The benefit of allowing arbitrary coefficient rings, is that the statements afterwards are clean,
and do not have `map (int.cast_ring_hom R)` interfering all the time.

## References

[Lionel Ponton, _Roots of the Chebyshev polynomials: A purely algebraic approach_]
[ponton2020chebyshev]

## TODO

* Redefine and/or relate the definition of Chebyshev polynomials to `linear_recurrence`.
* Add explicit formula involving square roots for Chebyshev polynomials
* Compute zeroes and extrema of Chebyshev polynomials.
* Prove that the roots of the Chebyshev polynomials (except 0) are irrational.
* Prove minimax properties of Chebyshev polynomials.
-/


noncomputable section

namespace Polynomial.Chebyshev

open Polynomial

open Polynomial

variable (R S : Type _) [CommRing R] [CommRing S]

/-- `t n` is the `n`-th Chebyshev polynomial of the first kind -/
noncomputable def t : ℕ → R[X]
  | 0 => 1
  | 1 => X
  | n + 2 => 2 * X * t (n + 1) - t n
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T Polynomial.Chebyshev.t

@[simp]
theorem t_zero : t R 0 = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_zero Polynomial.Chebyshev.t_zero

@[simp]
theorem t_one : t R 1 = X :=
  rfl
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_one Polynomial.Chebyshev.t_one

@[simp]
theorem t_add_two (n : ℕ) : t R (n + 2) = 2 * X * t R (n + 1) - t R n := by rw [t]
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_add_two Polynomial.Chebyshev.t_add_two

theorem t_two : t R 2 = 2 * X ^ 2 - 1 := by simp only [t, sub_left_inj, sq, mul_assoc]
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_two Polynomial.Chebyshev.t_two

theorem t_of_two_le (n : ℕ) (h : 2 ≤ n) : t R n = 2 * X * t R (n - 1) - t R (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact t_add_two R n
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_of_two_le Polynomial.Chebyshev.t_of_two_le

/-- `U n` is the `n`-th Chebyshev polynomial of the second kind -/
noncomputable def u : ℕ → R[X]
  | 0 => 1
  | 1 => 2 * X
  | n + 2 => 2 * X * u (n + 1) - u n
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U Polynomial.Chebyshev.u

@[simp]
theorem u_zero : u R 0 = 1 :=
  rfl
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U_zero Polynomial.Chebyshev.u_zero

@[simp]
theorem u_one : u R 1 = 2 * X :=
  rfl
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U_one Polynomial.Chebyshev.u_one

@[simp]
theorem u_add_two (n : ℕ) : u R (n + 2) = 2 * X * u R (n + 1) - u R n := by rw [u]
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U_add_two Polynomial.Chebyshev.u_add_two

theorem u_two : u R 2 = 4 * X ^ 2 - 1 := by
  simp only [u]
  ring
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U_two Polynomial.Chebyshev.u_two

theorem u_of_two_le (n : ℕ) (h : 2 ≤ n) : u R n = 2 * X * u R (n - 1) - u R (n - 2) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [add_comm]
  exact u_add_two R n
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U_of_two_le Polynomial.Chebyshev.u_of_two_le

theorem u_eq_x_mul_u_add_t : ∀ n : ℕ, u R (n + 1) = X * u R n + t R (n + 1)
  | 0 => by
    simp only [u_zero, u_one, t_one]
    ring_nf
    simp only [u_one, t_one]
    ring
  | 1 => by
    simp only [u_one, t_two]
    rw [u_two]
    ring_nf
    rw [t_two]
    ring
  | n + 2 =>
    calc
      u R (n + 2 + 1) = 2 * X * (X * u R (n + 1) + t R (n + 2)) - (X * u R n + t R (n + 1)) := by
        rw [u_add_two, u_eq_x_mul_u_add_t n, u_eq_x_mul_u_add_t (n + 1), u_eq_x_mul_u_add_t n]
      _ = X * (2 * X * u R (n + 1) - u R n) + (2 * X * t R (n + 2) - t R (n + 1)) := by ring
      _ = X * u R (n + 2) + t R (n + 2 + 1) := by simp only [u_add_two, t_add_two]

set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.U_eq_X_mul_U_add_T Polynomial.Chebyshev.u_eq_x_mul_u_add_t

theorem t_eq_u_sub_x_mul_u (n : ℕ) : t R (n + 1) = u R (n + 1) - X * u R n := by
  rw [u_eq_x_mul_u_add_t, add_comm (X * u R n), add_sub_cancel]
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_eq_U_sub_X_mul_U Polynomial.Chebyshev.t_eq_u_sub_x_mul_u

theorem t_eq_x_mul_t_sub_pol_u : ∀ n : ℕ, t R (n + 2) = X * t R (n + 1) - (1 - X ^ 2) * u R n
  | 0 => by
    simp only [t_one, t_two, u_zero]
    ring_nf
    simp only [t_one, t_two]
    ring
  | 1 => by
    simp only [t_add_two, t_zero, t_add_two, u_one, t_one]
    ring_nf
    simp only [t_one]
    ring
  | n + 2 =>
    calc
      t R (n + 2 + 2) = 2 * X * t R (n + 2 + 1) - t R (n + 2) := t_add_two _ _
      _ = 2 * X * (X * t R (n + 2) - (1 - X ^ 2) * u R (n + 1)) -
            (X * t R (n + 1) - (1 - X ^ 2) * u R n) :=
        by simp only [t_eq_x_mul_t_sub_pol_u]
      _ = X * (2 * X * t R (n + 2) - t R (n + 1)) - (1 - X ^ 2) * (2 * X * u R (n + 1) - u R n) :=
        by ring
      _ = X * t R (n + 2 + 1) - (1 - X ^ 2) * u R (n + 2) := by rw [t_add_two _ (n + 1), u_add_two]

set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_eq_X_mul_T_sub_pol_U Polynomial.Chebyshev.t_eq_x_mul_t_sub_pol_u

theorem one_sub_x_sq_mul_u_eq_pol_in_t (n : ℕ) :
    (1 - X ^ 2) * u R n = X * t R (n + 1) - t R (n + 2) := by
  rw [t_eq_x_mul_t_sub_pol_u, ← sub_add, sub_self, zero_add]
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.one_sub_X_sq_mul_U_eq_pol_in_T Polynomial.Chebyshev.one_sub_x_sq_mul_u_eq_pol_in_t

variable {R S}

@[simp]
theorem map_t (f : R →+* S) : ∀ n : ℕ, map f (t R n) = t S n
  | 0 => by simp only [t_zero, Polynomial.map_one]
  | 1 => by simp only [t_one, map_X]
  | n + 2 =>
    by
    have : (1 : R[X]) + 1 = 2 := by
      norm_num
    simp only [t_add_two, Polynomial.map_mul, Polynomial.map_sub, map_X]
    rw [← this]
    simp only [Polynomial.map_add, Polynomial.map_one]
    rw [map_t f (n + 1), map_t f n]
    norm_num
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.map_T Polynomial.Chebyshev.map_t

@[simp]
theorem map_u (f : R →+* S) : ∀ n : ℕ, map f (u R n) = u S n
  | 0 => by simp only [u_zero, Polynomial.map_one]
  | 1 =>
    by
    simp only [u_one, map_X, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_one]
    change map f (2) * X = 2 * X
    have : (1 : R[X]) + 1 = 2 := by
      norm_num
    rw [← this]
    simp only [Polynomial.map_add, Polynomial.map_one]
    norm_num
  | n + 2 =>
    by
    have : (1 : R[X]) + 1 = 2 := by
      norm_num
    simp only [u_add_two, Polynomial.map_mul, Polynomial.map_sub, map_X, ← this, Polynomial.map_add,
      Polynomial.map_one]
    rw [map_u f (n + 1), map_u f n]
    norm_num
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.map_U Polynomial.Chebyshev.map_u

theorem t_derivative_eq_u : ∀ n : ℕ, derivative (t R (n + 1)) = (n + 1) * u R n
  | 0 => by simp only [t_one, u_zero, derivative_X, Nat.cast_zero, zero_add, mul_one]
  | 1 =>
    by
    have : 1 + 1 = 2 := by norm_num
    rw [this, t_two, derivative_sub, derivative_one, derivative_mul]
    have : ((2 : ℕ) : R[X]) = (2:R[X]) := by norm_num
    rw [← this]
    -- TODO porting: simplify proof
    have : (@FunLike.coe (R →+* R[X]) R (fun _ => R[X]) MulHomClass.toFunLike C 2 : R[X])
        = (2 : R[X]) := by
         norm_cast
    simp only [derivative_nat_cast, derivative_mul, derivative_X_pow]
    simp only [t_two, u_one, derivative_sub, derivative_one, derivative_mul, derivative_X_pow,
      Nat.cast_one, Nat.cast_two]
    simp only [this]
    norm_num
  | n + 2 =>
    calc
      derivative (t R (n + 2 + 1)) =
          2 * t R (n + 2) + 2 * X * derivative (t R (n + 1 + 1)) - derivative (t R (n + 1)) :=
        by
          rw [t_add_two _ (n + 1), derivative_sub, derivative_mul, derivative_mul, derivative_X]
          have : (@FunLike.coe (R →+* R[X]) R (fun _ => R[X]) MulHomClass.toFunLike C 2 : R[X])
            = (2 : R[X]) := by
            norm_cast
          rw [← this, derivative_C]
          ring_nf
      _ = 2 * (u R (n + 1 + 1) - X * u R (n + 1)) + 2 * X * (((n + 1 + 1) : R[X]) * u R (n + 1))
          - ((n + 1) : R[X]) * u R n := by
        rw_mod_cast [t_derivative_eq_u (n + 1), t_derivative_eq_u n, t_eq_u_sub_x_mul_u _ (n + 1)]
      _ = (n + 1 : R[X]) * (2 * X * u R (n + 1) - u R n) + 2 * u R (n + 2) := by ring
      _ = (n + 1) * u R (n + 2) + 2 * u R (n + 2) := by rw [u_add_two]
      _ = (n + 2 + 1) * u R (n + 2) := by ring
      _ = (↑(n + 2) + 1) * u R (n + 2) := by norm_cast
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_derivative_eq_U Polynomial.Chebyshev.t_derivative_eq_u

theorem one_sub_x_sq_mul_derivative_t_eq_poly_in_t (n : ℕ) :
    (1 - X ^ 2) * derivative (t R (n + 1)) = (n + 1 : R[X]) * (t R n - X * t R (n + 1)) :=
  calc
    (1 - X ^ 2) * derivative (t R (n + 1)) = (1 - X ^ 2) * ((n + 1 : R[X]) * u R n) := by
      rw [t_derivative_eq_u]
    _ = (n + 1 : R[X]) * ((1 - X ^ 2) * u R n) := by ring
    _ = (n + 1 : R[X]) * (X * t R (n + 1) - (2 * X * t R (n + 1) - t R n)) := by
      rw [one_sub_x_sq_mul_u_eq_pol_in_t, t_add_two]
    _ = (n + 1 : R[X]) * (t R n - X * t R (n + 1)) := by ring

set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.one_sub_X_sq_mul_derivative_T_eq_poly_in_T Polynomial.Chebyshev.one_sub_x_sq_mul_derivative_t_eq_poly_in_t

theorem add_one_mul_t_eq_poly_in_u (n : ℕ) :
    ((n : R[X]) + 1) * t R (n + 1) = X * u R n - (1 - X ^ 2) * derivative (u R n) := by
  have h :
    derivative (t R (n + 2)) =
      u R (n + 1) - X * u R n + X * derivative (t R (n + 1)) + 2 * X * u R n -
        (1 - X ^ 2) * derivative (u R n) :=
    by
    conv_lhs => rw [t_eq_x_mul_t_sub_pol_u]
    simp only [derivative_sub, derivative_mul, derivative_X, derivative_one, derivative_X_pow,
      one_mul, t_derivative_eq_u]
    rw [t_eq_u_sub_x_mul_u, C_eq_nat_cast]
    ring
  calc
    ((n : R[X]) + 1) * t R (n + 1) =
        ((n : R[X]) + 1 + 1) * (X * u R n + t R (n + 1)) - X * ((n + 1 : R[X]) * u R n) -
          (X * u R n + t R (n + 1)) :=
      by ring
    _ = derivative (t R (n + 2)) - X * derivative (t R (n + 1)) - u R (n + 1) := by
      rw [← u_eq_x_mul_u_add_t, ← t_derivative_eq_u, ← Nat.cast_one, ← Nat.cast_add, Nat.cast_one, ←
        t_derivative_eq_u (n + 1)]
    _ = u R (n + 1) - X * u R n + X * derivative (t R (n + 1)) + 2 * X * u R n -
              (1 - X ^ 2) * derivative (u R n) -
            X * derivative (t R (n + 1)) -
          u R (n + 1) :=
      by rw [h]
    _ = X * u R n - (1 - X ^ 2) * derivative (u R n) := by ring

set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.add_one_mul_T_eq_poly_in_U Polynomial.Chebyshev.add_one_mul_t_eq_poly_in_u

variable (R)

/-- The product of two Chebyshev polynomials is the sum of two other Chebyshev polynomials. -/
theorem mul_t : ∀ m k, 2 * t R m * t R (m + k) = t R (2 * m + k) + t R k
  | 0 => by simp [two_mul, add_mul]
  | 1 => by simp [add_comm]
  | m + 2 => by
    intro k
    -- clean up the `T` nat indices in the goal
    suffices 2 * t R (m + 2) * t R (m + k + 2) = t R (2 * m + k + 4) + t R k
      by
      have h_nat₁ : 2 * (m + 2) + k = 2 * m + k + 4 := by ring
      have h_nat₂ : m + 2 + k = m + k + 2 := by ring
      simpa [h_nat₁, h_nat₂] using this
    -- clean up the `T` nat indices in the inductive hypothesis applied to `m + 1` and
    -- `k + 1`
    have H₁ : 2 * t R (m + 1) * t R (m + k + 2) = t R (2 * m + k + 3) + t R (k + 1) :=
      by
      have h_nat₁ : m + 1 + (k + 1) = m + k + 2 := by ring
      have h_nat₂ : 2 * (m + 1) + (k + 1) = 2 * m + k + 3 := by ring
      simpa [h_nat₁, h_nat₂] using mul_t (m + 1) (k + 1)
    -- clean up the `T` nat indices in the inductive hypothesis applied to `m` and `k + 2`
    have H₂ : 2 * t R m * t R (m + k + 2) = t R (2 * m + k + 2) + t R (k + 2) :=
      by
      have h_nat₁ : 2 * m + (k + 2) = 2 * m + k + 2 := by simp [add_assoc]
      have h_nat₂ : m + (k + 2) = m + k + 2 := by simp [add_assoc]
      simpa [h_nat₁, h_nat₂] using mul_t m (k + 2)
    -- state the `T` recurrence relation for a few useful indices
    have h₁ := t_add_two R m
    have h₂ := t_add_two R (2 * m + k + 2)
    have h₃ := t_add_two R k
    -- the desired identity is an appropriate linear combination of H₁, H₂, h₁, h₂, h₃
    linear_combination 2 * t R (m + k + 2) * h₁ + 2 * (X : R[X]) * H₁ - H₂ - h₂ - h₃
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.mul_T Polynomial.Chebyshev.mul_t

/-- The `(m * n)`-th Chebyshev polynomial is the composition of the `m`-th and `n`-th -/
theorem t_mul : ∀ m n, t R (m * n) = (t R m).comp (t R n)
  | 0 => by simp
  | 1 => by simp
  | m + 2 => by
    intro n
    have : 2 * t R n * t R ((m + 1) * n) = t R ((m + 2) * n) + t R (m * n) := by
      convert mul_t R n (m * n) <;> ring
    simp [this, t_mul m, ← t_mul (m + 1)]
set_option linter.uppercaseLean3 false in
#align polynomial.chebyshev.T_mul Polynomial.Chebyshev.t_mul

end Polynomial.Chebyshev

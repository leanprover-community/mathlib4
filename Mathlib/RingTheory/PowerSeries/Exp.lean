/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.RingTheory.PowerSeries.Derivative

/-!
# Exponential Power Series

This file defines the exponential power series `exp A = ∑ Xⁿ/n!` over ℚ-algebras and develops
its key properties, including the fundamental differential equation `(exp A)' = exp A`,
a uniqueness characterization, and the functional equation for multiplication.

## Main definitions

* `PowerSeries.exp`: The exponential power series `exp A = ∑ Xⁿ/n!` over a ℚ-algebra `A`.

## Main results

* `PowerSeries.coeff_exp`: The coefficient of `exp A` at `n` is `1/n!`.
* `PowerSeries.constantCoeff_exp`: The constant term of `exp A` is `1`.
* `PowerSeries.map_exp`: `exp` is preserved by ring homomorphisms between ℚ-algebras.
* `PowerSeries.derivative_exp`: The derivative of exp equals exp: `d⁄dX A (exp A) = exp A`.
* `PowerSeries.exp_unique_of_derivative_eq_self`: A power series with derivative equal to itself
  and constant term `1` must be `exp`.
* `PowerSeries.isUnit_exp`: `exp A` is a unit (invertible).
* `PowerSeries.order_exp`: The order of `exp A` is `0`.
* `PowerSeries.exp_mul_exp_eq_exp_add`: The functional equation `e^{aX} * e^{bX} = e^{(a+b)X}`.
* `PowerSeries.exp_mul_exp_neg_eq_one`: The identity `e^X * e^{-X} = 1`.
* `PowerSeries.exp_pow_eq_rescale_exp`: Powers of exp satisfy `(e^X)^k = e^{kX}`.
* `PowerSeries.exp_pow_sum`: Formula for the sum of powers of `exp`.
-/

@[expose] public section

namespace PowerSeries

variable (A A' : Type*) [Ring A] [Ring A'] [Algebra ℚ A] [Algebra ℚ A']

open Nat

/-- Power series for the exponential function at zero. -/
def exp : PowerSeries A :=
  mk fun n => algebraMap ℚ A (1 / n !)

variable {A A'} (n : ℕ) (f : A →+* A')

@[simp]
theorem coeff_exp : coeff n (exp A) = algebraMap ℚ A (1 / n !) :=
  coeff_mk _ _

@[simp]
theorem constantCoeff_exp : constantCoeff (exp A) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_exp]
  simp

@[simp]
theorem map_exp : map (f : A →+* A') (exp A) = exp A' := by
  ext
  simp

/-! ### Derivative of exp -/

theorem derivative_exp (A : Type*) [CommRing A] [Algebra ℚ A] :
    d⁄dX A (exp A) = exp A := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_exp]
  have key : (n + 1 : A) = algebraMap ℚ A (n + 1) := by
    rw [map_add, map_natCast, map_one]
  rw [key, ← map_mul, factorial_succ, Nat.cast_mul, Nat.cast_add_one]
  congr 1
  field_simp

/-! ### Uniqueness characterization -/

variable {A : Type*}

/-- A power series with derivative equal to itself and constant term 1 must be `exp`.

The proof uses induction on coefficients: if `f' = f` and `f(0) = 1`, then
`coeff (n+1) f * (n+1) = coeff n f`, which determines all coefficients uniquely. -/
theorem exp_unique_of_derivative_eq_self [CommRing A] [Algebra ℚ A] [IsAddTorsionFree A]
    {f : PowerSeries A} (hd : d⁄dX A f = f) (hc : constantCoeff f = 1) :
    f = exp A := by
  ext n
  induction n with
  | zero =>
    rw [coeff_zero_eq_constantCoeff, hc, constantCoeff_exp]
  | succ n ih =>
    have eq1 : coeff n (d⁄dX A f) = coeff n f := congrArg (coeff n) hd
    rw [coeff_derivative] at eq1
    have eq2 : coeff n (d⁄dX A (exp A)) = coeff n (exp A) := congrArg (coeff n) (derivative_exp A)
    rw [coeff_derivative] at eq2
    rw [ih] at eq1
    have h : coeff (n + 1) f * (n + 1) = coeff (n + 1) (exp A) * (n + 1) := by
      rw [eq1, eq2]
    rw [← Nat.cast_succ, mul_comm, ← nsmul_eq_mul, mul_comm, ← nsmul_eq_mul] at h
    exact (smul_right_inj (Nat.succ_ne_zero n)).mp h

/-! ### Order and invertibility -/

theorem isUnit_exp (A : Type*) [Ring A] [Algebra ℚ A] : IsUnit (exp A) :=
  isUnit_iff_constantCoeff.mpr (by simp)

@[simp]
theorem order_exp (A : Type*) [Ring A] [Algebra ℚ A] [Nontrivial A] : (exp A).order = 0 :=
  order_zero_of_unit (isUnit_exp A)


open RingHom

open Finset Nat

variable {A : Type*} [CommRing A]

/-- Shows that $e^{aX} * e^{bX} = e^{(a + b)X}$ -/
theorem exp_mul_exp_eq_exp_add [Algebra ℚ A] (a b : A) :
    rescale a (exp A) * rescale b (exp A) = rescale (a + b) (exp A) := by
  ext n
  simp only [coeff_mul, exp, rescale, coeff_mk, MonoidHom.coe_mk, OneHom.coe_mk, coe_mk,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk, add_pow, sum_mul]
  apply sum_congr rfl
  rintro x hx
  suffices
    a ^ x * b ^ (n - x) *
        (algebraMap ℚ A (1 / ↑x.factorial) * algebraMap ℚ A (1 / ↑(n - x).factorial)) =
      a ^ x * b ^ (n - x) * (↑(n.choose x) * (algebraMap ℚ A) (1 / ↑n.factorial))
    by convert this using 1 <;> ring
  congr 1
  rw [← map_natCast (algebraMap ℚ A) (n.choose x), ← map_mul, ← map_mul]
  refine RingHom.congr_arg _ ?_
  rw [mul_one_div (↑(n.choose x) : ℚ), one_div_mul_one_div]
  symm
  rw [div_eq_iff, div_mul_eq_mul_div, one_mul, choose_eq_factorial_div_factorial]
  · norm_cast
    rw [cast_div_charZero]
    apply factorial_mul_factorial_dvd_factorial (mem_range_succ_iff.1 hx)
  · apply mem_range_succ_iff.1 hx
  · rintro h
    apply factorial_ne_zero n
    rw [cast_eq_zero.1 h]

/-- Shows that $e^{x} * e^{-x} = 1$ -/
theorem exp_mul_exp_neg_eq_one [Algebra ℚ A] : exp A * evalNegHom (exp A) = 1 := by
  convert exp_mul_exp_eq_exp_add (1 : A) (-1) <;> simp

/-- Shows that $(e^{X})^k = e^{kX}$. -/
theorem exp_pow_eq_rescale_exp [Algebra ℚ A] (k : ℕ) : exp A ^ k = rescale (k : A) (exp A) := by
  induction k with
  | zero =>
    simp only [rescale_zero, constantCoeff_exp, Function.comp_apply, map_one, cast_zero,
      pow_zero (exp A), coe_comp]
  | succ k h =>
    simpa only [succ_eq_add_one, cast_add, ← exp_mul_exp_eq_exp_add (k : A), ← h, cast_one,
      id_apply, rescale_one] using pow_succ (exp A) k

/-- Shows that
$\sum_{k = 0}^{n - 1} (e^{X})^k = \sum_{p = 0}^{\infty} \sum_{k = 0}^{n - 1} \frac{k^p}{p!}X^p$. -/
theorem exp_pow_sum [Algebra ℚ A] (n : ℕ) :
    ((Finset.range n).sum fun k => exp A ^ k) =
      PowerSeries.mk fun p => (Finset.range n).sum
        fun k => (k ^ p : A) * algebraMap ℚ A p.factorial⁻¹ := by
  simp only [exp_pow_eq_rescale_exp, rescale]
  ext
  simp only [one_div, coeff_mk, coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    coeff_exp, map_sum]

end PowerSeries

end

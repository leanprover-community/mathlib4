/-
Copyright (c) 2026 Mathlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mathlib contributors
-/
module

public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Data.Nat.Cast.Field
public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Exponential Power Series

This file defines the exponential power series `exp A = ∑ Xⁿ/n!` over ℚ-algebras.

## Main definitions

* `PowerSeries.exp`: The exponential power series `exp A = ∑ Xⁿ/n!` over a ℚ-algebra `A`.

## Main results

* `PowerSeries.coeff_exp`: The coefficient of `exp A` at `n` is `1/n!`.
* `PowerSeries.constantCoeff_exp`: The constant term of `exp A` is `1`.
* `PowerSeries.map_exp`: `exp` is preserved by ring homomorphisms between ℚ-algebras.
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

variable {A A'} (n : ℕ)

variable (f : A →+* A')

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

/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Interval
import Mathlib.Algebra.MvPolynomial.Eval

/-!

# Formal (multivariate) power series - Truncation

* `MvPowerSeries.trunc n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m < n`, and `0` otherwise.

  Note that here, `m` and `n` have types `σ →₀ ℕ`,
  so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

* `MvPowerSeries.trunc_one` : truncation of the unit power series

* `MvPowerSeries.trunc_C` : truncation of a constant

* `MvPowerSeries.trunc_C_mul` : truncation of constant multiple.

* `MvPowerSeries.trunc' n φ` truncates a formal multivariate power series
  to the multivariate polynomial that has the same coefficients as `φ`,
  for all `m ≤ n`, and `0` otherwise.

  Here, `m` and `n`  have types `σ →₀ ℕ` so that `m ≤ n` means that `m s ≤ n s` for all `s : σ`.


* `MvPowerSeries.coeff_mul_eq_coeff_trunc'_mul_trunc'` : compares the coefficients
  of a product with those of the product of truncations.

* `MvPowerSeries.trunc'_one` : truncation of a the unit power series.

* `MvPowerSeries.trunc'_C` : truncation of a constant.

* `MvPowerSeries.trunc'_C_mul` : truncation of a constant multiple.

* `MvPowerSeries.trunc'_map` : image of a truncation under a change of rings

## TODO

* Unify both versions using a general purpose API

-/


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R S : Type*}

section TruncLT

variable [DecidableEq σ] [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iio n, MvPolynomial.monomial m (coeff R m φ)

theorem coeff_truncFun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical
  simp [truncFun, MvPolynomial.coeff_sum]

variable (R) in
/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable power series obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`
and $a i < n i` for some `i`. -/
def trunc : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun n
  map_zero' := by
    classical
    ext
    simp [coeff_truncFun]
  map_add' := by
    classical
    intros x y
    ext m
    simp only [coeff_truncFun, MvPolynomial.coeff_add, ite_add_ite, ← map_add, add_zero]

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical simp [trunc, coeff_truncFun]

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc, coeff_one]
    split_ifs with H H'
    · subst m
      simp
    · symm
      rw [MvPolynomial.coeff_one]
      exact if_neg (Ne.symm H')
    · symm
      rw [MvPolynomial.coeff_one]
      refine if_neg ?_
      rintro rfl
      apply H
      exact Ne.bot_lt hnn

@[simp]
theorem trunc_C (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all only [ne_eq, not_true_eq_false]
    exfalso; apply H; subst m; exact Ne.bot_lt hnn

@[simp]
theorem trunc_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc R n (C σ R a * p) = MvPolynomial.C a * trunc R n p := by
  ext m; simp [coeff_trunc]

@[simp]
theorem trunc_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc S n (map σ f p) = MvPolynomial.map f (trunc R n p) := by
  ext m; simp [coeff_trunc, MvPolynomial.coeff_map, apply_ite f]

end TruncLT

section TruncLE

variable [DecidableEq σ] [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun' (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iic n, MvPolynomial.monomial m (coeff R m φ)

/-- Coefficients of the truncated function. -/
theorem coeff_truncFun' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun' n φ).coeff m = if m ≤ n then coeff R m φ else 0 := by
  classical
  simp [truncFun', MvPolynomial.coeff_sum]

variable (R) in
/--
The `n`th truncation of a multivariate formal power series to a multivariate polynomial.

If `f : MvPowerSeries σ R` and `n : σ →₀ ℕ` is a (finitely-supported) function from `σ`
to the naturals, then `trunc' R n f` is the multivariable power series obtained from `f`
by keeping only the monomials $c\prod_i X_i^{a_i}$ where `a i ≤ n i` for all `i`. -/
def trunc' : MvPowerSeries σ R →+ MvPolynomial σ R where
  toFun := truncFun' n
  map_zero' := by
    ext
    simp only [coeff_truncFun', map_zero, ite_self, MvPolynomial.coeff_zero]
  map_add' x y := by
    ext m
    simp only [coeff_truncFun', MvPolynomial.coeff_add]
    rw [ite_add_ite, ← map_add, zero_add]

/-- Coefficients of the truncation of a multivariate power series. -/
theorem coeff_trunc' (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc' R n φ).coeff m = if m ≤ n then coeff R m φ else 0 :=
  coeff_truncFun' n m φ

/-- Truncation of the multivariate power series `1` -/
@[simp]
theorem trunc'_one (n : σ →₀ ℕ) : trunc' R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc', coeff_one]
    split_ifs with H H'
    · subst m; simp only [MvPolynomial.coeff_zero_one]
    · rw [MvPolynomial.coeff_one, if_neg (Ne.symm H')]
    · rw [MvPolynomial.coeff_one, if_neg ?_]
      rintro rfl
      exact H (zero_le n)

@[simp]
theorem trunc'_C (n : σ →₀ ℕ) (a : R) :
    trunc' R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m ↦ by
    classical
    rw [coeff_trunc', coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first | rfl | try simp_all
    exfalso; apply H; subst m; exact zero_le n

/-- Coefficients of the truncation of a product of two multivariate power series -/
theorem coeff_mul_eq_coeff_trunc'_mul_trunc' (n : σ →₀ ℕ)
    (f g : MvPowerSeries σ R) {m : σ →₀ ℕ} (h : m ≤ n) :
    coeff R m (f * g) = ((trunc' R n f) * (trunc' R n g)).coeff m := by
  classical
  simp only [MvPowerSeries.coeff_mul, MvPolynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  simp only [mem_antidiagonal] at hij
  rw [← hij] at h
  simp only
  apply congr_arg₂
  · rw [coeff_trunc', if_pos (le_trans le_self_add h)]
  · rw [coeff_trunc', if_pos (le_trans le_add_self h)]

@[simp]
theorem trunc'_C_mul (n : σ →₀ ℕ) (a : R) (p : MvPowerSeries σ R) :
    trunc' R n (C σ R a * p) = MvPolynomial.C a * trunc' R n p := by
  ext m; simp [coeff_trunc']

@[simp]
theorem trunc'_map [CommSemiring S] (n : σ →₀ ℕ) (f : R →+* S) (p : MvPowerSeries σ R) :
    trunc' S n (map σ f p) = MvPolynomial.map f (trunc' R n p) := by
  ext m; simp [coeff_trunc', MvPolynomial.coeff_map, apply_ite f]

end TruncLE

end MvPowerSeries

end

/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Kenny Lau
-/

import Mathlib.RingTheory.MvPowerSeries.Basic
import Mathlib.Data.Finsupp.Interval

/-!

# Formal (multivariate) power series - Truncation

`MvPowerSeries.trunc n φ` truncates a formal multivariate power series
to the multivariate polynomial that has the same coefficients as `φ`,
for all `m < n`, and `0` otherwise.

Note that here, `m` and `n` have types `σ →₀ ℕ`,
so that `m < n` means that `m ≠ n` and `m s ≤ n s` for all `s : σ`.

-/


noncomputable section

open Finset (antidiagonal mem_antidiagonal)

namespace MvPowerSeries

open Finsupp

variable {σ R : Type*}

section Trunc

variable [CommSemiring R] (n : σ →₀ ℕ)

/-- Auxiliary definition for the truncation function. -/
def truncFun (φ : MvPowerSeries σ R) : MvPolynomial σ R :=
  ∑ m ∈ Finset.Iio n, MvPolynomial.monomial m (coeff R m φ)
#align mv_power_series.trunc_fun MvPowerSeries.truncFun

theorem coeff_truncFun (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (truncFun n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical
  simp [truncFun, MvPolynomial.coeff_sum]
#align mv_power_series.coeff_trunc_fun MvPowerSeries.coeff_truncFun

variable (R)

/-- The `n`th truncation of a multivariate formal power series to a multivariate polynomial -/
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
    simp only [coeff_truncFun, MvPolynomial.coeff_add]
    split_ifs
    · rw [map_add]
    · rw [zero_add]

#align mv_power_series.trunc MvPowerSeries.trunc

variable {R}

theorem coeff_trunc (m : σ →₀ ℕ) (φ : MvPowerSeries σ R) :
    (trunc R n φ).coeff m = if m < n then coeff R m φ else 0 := by
  classical simp [trunc, coeff_truncFun]
#align mv_power_series.coeff_trunc MvPowerSeries.coeff_trunc

@[simp]
theorem trunc_one (n : σ →₀ ℕ) (hnn : n ≠ 0) : trunc R n 1 = 1 :=
  MvPolynomial.ext _ _ fun m => by
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
#align mv_power_series.trunc_one MvPowerSeries.trunc_one

@[simp]
theorem trunc_c (n : σ →₀ ℕ) (hnn : n ≠ 0) (a : R) : trunc R n (C σ R a) = MvPolynomial.C a :=
  MvPolynomial.ext _ _ fun m => by
    classical
    rw [coeff_trunc, coeff_C, MvPolynomial.coeff_C]
    split_ifs with H <;> first |rfl|try simp_all
    exfalso; apply H; subst m; exact Ne.bot_lt hnn
set_option linter.uppercaseLean3 false in
#align mv_power_series.trunc_C MvPowerSeries.trunc_c

end Trunc

end MvPowerSeries

end

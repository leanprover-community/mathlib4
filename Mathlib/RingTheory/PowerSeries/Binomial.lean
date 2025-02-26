/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Eval
import Mathlib.RingTheory.Binomial

/-!
# Binomial Power Series
We introduce formal power series of the form `(1 + X f(X)) ^ r`, where `r` is an element of a
commutative binomial ring `R`, and `f(X)` is a formal power series with coefficients in a
commutative `R`-algebra. This formal exponentiation operation makes the group `1 + XR[[X]]` into an
`R`-module.

## Main Definitions
  * `BinomialPow`?

## Main results

  * coefficients of powers of binomials

## To do

Use RingTheory.PowerSeries.Eval

-/

open Finset Function

open scoped Classical
open BigOperators Pointwise

suppress_compilation

variable {Γ R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

/-- The power series for `(1 + X) ^ r`. -/
def BinomialSeries (r : R) : PowerSeries R :=
  mk fun n => Ring.choose r n

@[simp]
lemma binomial_coeff (r : R) (n : ℕ) : (coeff R n) (BinomialSeries r) = Ring.choose r n := by
  dsimp only [BinomialSeries]
  exact coeff_mk n fun n ↦ Ring.choose r n

@[simp]
lemma binomial_add (r s : R) : BinomialSeries (r + s) = BinomialSeries r * BinomialSeries s := by
  ext n
  simp only [binomialSeries_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm, mul_smul]

@[simp]
lemma binomialSeries_nat [CommRing A] (d : ℕ) :
    binomialSeries A (d : ℤ) = (1 + X) ^ d := by
  ext n
  by_cases h : d < n
  · rw [binomialSeries_coeff, add_comm, add_pow, map_sum, Ring.choose_natCast, natCast_zsmul,
      Nat.choose_eq_zero_of_lt h, zero_nsmul, sum_eq_zero]
    intro k hk
    rw [one_pow, mul_one, coeff_X_pow_mul']
    have hkd : k ≤ d := mem_range_succ_iff.mp hk
    simp only [hkd.trans (le_of_lt h), ↓reduceIte]
    rw [← map_natCast (C A), coeff_ne_zero_C (by omega)]
  · rw [binomialSeries_coeff, add_comm, add_pow]
    simp only [zsmul_eq_mul, mul_one, one_pow, map_sum]
    rw [sum_eq_single_of_mem n (by simp only [mem_range]; omega) ?_, coeff_X_pow_mul',
      Ring.choose_eq_nat_choose]
    · simp
    · intro k hk hkn
      rw [mul_comm, ← map_natCast (C A), coeff_C_mul_X_pow]
      exact if_neg (Ne.symm hkn)

lemma rescale_neg_one_invOneSubPow [CommRing A] (d : ℕ) :
    rescale (-1 : A) (invOneSubPow A d) = binomialSeries A (-d : ℤ) := by
  ext n
  rw [coeff_rescale, binomialSeries_coeff, ← Int.cast_negOnePow_natCast, ← zsmul_eq_mul]
  cases d with
  | zero =>
    by_cases hn : n = 0 <;> simp [invOneSubPow, Ring.choose_zero_ite, hn]
  | succ d =>
    simp only [invOneSubPow, coeff_mk, Nat.cast_add, Nat.cast_one, neg_add_rev, Int.reduceNeg,
      zsmul_eq_mul, mul_one]
    rw [show (-1 : ℤ) + -d = -(d + 1) by abel, Ring.choose_neg, Nat.choose_symm_add, Units.smul_def,
      show (d : ℤ) + 1 + n - 1 = d + n by omega, ← Nat.cast_add, Ring.choose_eq_nat_choose]
    norm_cast

end PowerSeries

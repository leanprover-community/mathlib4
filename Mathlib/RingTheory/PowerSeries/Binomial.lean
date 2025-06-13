/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.WellKnown

/-!
# Binomial Power Series
We introduce formal power series of the form `(1 + X) ^ r`, where `r` is an element of a
commutative binomial ring `R`.

## Main Definitions
* `PowerSeries.binomialSeries`: A power series expansion of `(1 + X) ^ r`, where `r` is an element
  of a commutative binomial ring `R`.

## Main Results
* `PowerSeries.binomial_add`: Adding exponents yields multiplication of series.
* `PowerSeries.binomialSeries_nat`: when `r` is a natural number, we get `(1 + X) ^ r`.
* `PowerSeries.rescale_neg_one_invOneSubPow`: The image of `(1 - X) ^ (-d)` under the map
  `X ↦ (-X)` is `(1 + X) ^ (-d)`

## TODO
* When `A` is a commutative `R`-algebra, the exponentiation action makes the multiplicative group
  `1 + XA[[X]]` into an `R`-module.

-/

open Finset BigOperators

suppress_compilation

variable {R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

/-- The power series for `(1 + X) ^ r`. -/
def binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A :=
  mk fun n => Ring.choose r n • 1

@[simp]
lemma binomialSeries_coeff [Semiring A] [SMul R A] (r : R) (n : ℕ) :
    (coeff A n) (binomialSeries A r) = Ring.choose r n • 1 :=
  coeff_mk n fun n ↦ Ring.choose r n • 1

@[simp]
lemma binomialSeries_add [Semiring A] [Algebra R A] (r s : R) :
    binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s := by
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

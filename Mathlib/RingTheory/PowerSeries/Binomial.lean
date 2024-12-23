/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Binomial Power Series
We introduce formal power series of the form `(1 + X) ^ r`, where `r` is an element of a
commutative binomial ring `R`.

## Main Definitions
 * `PowerSeries.binomialSeries`: A power series expansion of

## Main results
 * `PowerSeries.binomial_add`: Adding exponents yields multiplication of series.

## To do
 * Comparison with `PowerSeries.invOneSubPow`
 * When `A` is a commutative `R`-algebra, exponentiation makes the group `1 + XA[[X]]` into an
   `R`-module.

-/

open Finset Function

open scoped Classical
open BigOperators Pointwise

suppress_compilation

variable {Γ R A : Type*}

namespace PowerSeries

variable [CommRing R] [BinomialRing R]

/-- The power series for `(1 + X) ^ r`. -/
def binomialSeries (A) [One A] [SMul R A] (r : R) : PowerSeries A :=
  mk fun n => Ring.choose r n • 1

@[simp]
lemma binomial_coeff [Semiring A] [SMul R A] (r : R) (n : ℕ) :
    (coeff A n) (binomialSeries A r) = Ring.choose r n • 1 := by
  dsimp only [binomialSeries]
  exact coeff_mk n fun n ↦ Ring.choose r n • 1

@[simp]
lemma binomial_add [Semiring A] [Algebra R A] (r s : R) :
    binomialSeries A (r + s) = binomialSeries A r * binomialSeries A s := by
  ext n
  simp only [binomial_coeff, Ring.add_choose_eq n (Commute.all r s), coeff_mul,
    Algebra.mul_smul_comm, mul_one, sum_smul]
  refine sum_congr rfl fun ab hab => ?_
  rw [mul_comm, mul_smul]

end PowerSeries

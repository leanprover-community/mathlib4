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
  simp [coeff_mul, Ring.add_choose_eq n (Commute.all r s)]

/-!
lemma binomialSeries_mul (r : R) : -- need mvPowerSeries
    (1 + (X 1)) ^ r * (1 + (X 2)) ^ r = (1 + (X 1) + (X 2) + (X 1) * (X 2)) ^ r := by
-/

/-- The power series given by `(1 + X * f X) ^ r`. -/
def BinomialEval (f : PowerSeries R) (r : R) : PowerSeries R :=
  eval f (BinomialSeries r)

/-!
/-- `(1 + X) ^ (r * s) = ((1 + X) ^ r) ^ s` -/
lemma binomial_mul (r s : R) :
    BinomialSeries (r * s) = BinomialEval (mk fun n => Ring.choose r (n + 1)) s := by
  ext n
  simp only [binomial_coeff, BinomialEval, eval_coeff, smul_eq_mul]
  rw [some_theorem_about_(r*s).choose]

-/

end PowerSeries

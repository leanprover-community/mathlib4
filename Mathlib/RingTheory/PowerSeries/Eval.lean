/-
Copyright (c) 2024 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Evaluating Power Series
We produce an algebra homomorphism from a power series ring `R[[X]]` to itself by substituting `X`
into a positive order element.

## Main Definitions
  * `PowerSeries.eval`

## Main results


## To do

-/


suppress_compilation

variable {Γ R A : Type*}

open Finset (antidiagonal mem_antidiagonal)

namespace PowerSeries

/-- Send a pair `(f, g)` of power series to `g(X * f(X))`. -/
def eval [Semiring R] (f g : PowerSeries R) : PowerSeries R :=
  mk (fun n => ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1))

@[simp]
lemma eval_coeff [Semiring R] (f g : PowerSeries R) (n : ℕ) :
    (coeff R n) (eval f g) = ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1) :=
  coeff_mk n fun n ↦ ∑ i ∈ antidiagonal n, (coeff R i.1 g) • coeff R i.2 (f ^ i.1)

@[simp]
lemma eval_add [Semiring R] (f g h : PowerSeries R) : eval f (g + h) = eval f g + eval f h := by
  ext n
  simp [add_mul, Finset.sum_add_distrib]

@[simp]
lemma eval_smul [Semiring R] (f g : PowerSeries R) (r : R) : eval f (r • g) = r • eval f g := by
  ext n
  simp [Finset.mul_sum, mul_assoc]

end PowerSeries

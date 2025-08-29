/-
Copyright (c) 2025 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Batteries.Data.Rat.Float

/-!
# Chudnovsky's formula for π

This file defines the infinite sum in Chudnovsky's formula for computing π⁻¹.
It does not (yet!) contain a proof; anyone is welcome to adopt this problem.

## Main definitions

* `chudnovskySum` : The infinite sum in Chudnovsky's formula

## Future work

* Prove the sum equals π⁻¹, as stated using `proof_wanted` below.
* Show that each imaginary quadratic field of class number 1 (corresponding to Heegner numbers)
  gives a Ramanujan type formula, and that this is the formula coming from 163,
  with $$j(\frac{1+\sqrt{-163}}{2}) = -640320^3$$, and the other magic constants coming from
  Eisenstein series.

## References
* https://arxiv.org/abs/1809.00533
* https://doi.org/10.1007/s11139-017-9948-8

-/

open scoped Real BigOperators
open Nat

/-- The numerator of the nth term in Chudnovsky's series -/
def chudnovskyNum (n : ℕ) : ℤ :=
  (-1 : ℤ) ^ n * (6 * n)! * (545140134 * n + 13591409)

/-- The denominator of the nth term in Chudnovsky's series -/
def chudnovskyDenom (n : ℕ) : ℕ :=
  (3 * n)! * (n)! ^ 3 * 640320 ^ (3 * n)

/-- The term at index n in Chudnovsky's series for π⁻¹ -/
def chudnovskyTerm (n : ℕ) : ℚ :=
  chudnovskyNum n / chudnovskyDenom n

-- Sanity check that when calculated in `Float` we get the right answer:
/-- info: 3.141593 -/
#guard_msgs in
#eval 1 / (12 / (640320 : Float) ^ (3 / 2) *
  (List.ofFn fun n : Fin 37 => (chudnovskyTerm n).toFloat).sum)

/-- The infinite sum in Chudnovsky's formula for π⁻¹ -/
noncomputable def chudnovskySum : ℝ :=
  12 / (640320 : ℝ) ^ (3 / 2) * ∑' n : ℕ, (chudnovskyTerm n : ℝ)

/-- **Chudnovsky's formula**: The sum equals π⁻¹ -/
proof_wanted chudnovskySum_eq_pi_inv : chudnovskySum = π⁻¹

/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.SparsePoly
import Mathlib.Tactic.ComputablePolynomial.Reflect
import Mathlib.Tactic.ComputablePolynomial.DvdCert
import Mathlib.Tactic.ComputablePolynomial.Tactics

/-!
# Tests for the computable univariate polynomial tactics

Examples exercising `poly_decide`, `poly_eval`, `poly_dvd`, and `poly_dvd_cert`. Each is proved
**axiom-free**: the `#print axioms` checks below confirm only `[propext, Classical.choice,
Quot.sound]` — in particular no `Lean.ofReduceBool` and no `native_decide`.
-/

open Polynomial

/-! ## `poly_decide` — polynomial identities by reflection -/

example : ((X + C 1) ^ 2 : Polynomial ℤ) = X ^ 2 + C 2 * X + C 1 := by poly_decide
example : (X ^ 2 - C 1 : Polynomial ℤ) = (X - C 1) * (X + C 1) := by poly_decide
example : ((X + C 1) ^ 3 : Polynomial ℤ) = X ^ 3 + C 3 * X ^ 2 + C 3 * X + C 1 := by poly_decide
example : (X ^ 2 - C 1 - (X - C 1) * (X + C 1) : Polynomial ℤ) = 0 := by poly_decide
-- bare numerals (no `C`) also work, axiom-free:
example : ((X + 1) * (X + 2) : Polynomial ℤ) = X ^ 2 + 3 * X + 2 := by poly_decide

-- The trust check: only the three standard axioms — no `Lean.ofReduceBool`.
theorem sq_expand : ((X + C 1) ^ 2 : Polynomial ℤ) = X ^ 2 + C 2 * X + C 1 := by poly_decide
/-- info: 'sq_expand' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms sq_expand

/-! ## `poly_dvd_cert` — divisibility by symbolic certificate -/

-- Monic divisor over `ℚ`:
example : (X - 1 : Polynomial ℚ) ∣ (X ^ 2 - 1) := by poly_dvd_cert
example : (X ^ 2 + X + 1 : Polynomial ℚ) ∣ (X ^ 3 - 1) := by poly_dvd_cert

-- Non-monic divisor with genuinely rational quotient (`2X − 2 ∣ X² − 1`, quotient `X/2 + 1/2`):
example : (2 * X - 2 : Polynomial ℚ) ∣ (X ^ 2 - 1) := by poly_dvd_cert

-- Monic divisor over a non-field commutative ring (`ℤ[X]`) — no field, no side goal:
example : (X - 1 : Polynomial ℤ) ∣ (X ^ 2 - 1) := by poly_dvd_cert

-- Symbolic monic divisor over an arbitrary commutative ring — no `Field`, no side goal:
example {R : Type*} [CommRing R] (a : R) : (X - C a : Polynomial R) ∣ (X ^ 2 - C (a ^ 2)) := by
  poly_dvd_cert

-- Symbolic coefficients, several at once:
example {K : Type*} [Field K] (a b : K) :
    (X - C a : Polynomial K) ∣ ((X - C a) * (X - C b)) := by poly_dvd_cert

-- Higher-degree symbolic monic divisor:
example {K : Type*} [Field K] (a : K) :
    (X ^ 2 - C (a ^ 2) : Polynomial K) ∣ (X ^ 4 - C (a ^ 4)) := by poly_dvd_cert

-- Arbitrary field, symbolic *non-monic* divisor — the `lc ≠ 0` side goal is discharged from `hu`:
example {K : Type*} [Field K] (u : K) (hu : u ≠ 0) :
    (C u * X - C u : Polynomial K) ∣ (X ^ 2 - 1) := by poly_dvd_cert

-- Non-monic over a non-field comm ring, unit leading coefficient `-1` (`ℤ[X]`):
example : (1 - X : Polynomial ℤ) ∣ (X ^ 2 - 1) := by poly_dvd_cert

-- Non-monic over a comm ring with an `IsUnit` hypothesis — no field needed:
example {R : Type*} [CommRing R] (u : R) (hu : IsUnit u) :
    (C u * X - C u : Polynomial R) ∣ (X ^ 2 - 1) := by poly_dvd_cert

-- A bigger one, instantly (compiled `MetaM` search; only the `ring` check is verified):
theorem big_dvd : (X - 1 : Polynomial ℚ) ∣ (X ^ 6 - 1) := by poly_dvd_cert
/-- info: 'big_dvd' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms big_dvd

/-! ## `poly_eval` and `poly_dvd` — kernel evaluation and divisibility -/

-- Evaluation: `(X² + 1)(2) = 5`:
example : Polynomial.eval 2 (X ^ 2 + 1 : Polynomial ℤ) = 5 := by poly_eval

-- A root: `2` is a root of `X² − 4`:
theorem root_demo : Polynomial.eval 2 (X ^ 2 - 4 : Polynomial ℤ) = 0 := by poly_eval
/-- info: 'root_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms root_demo

-- Divisibility over `ℤ` (kernel reduces `ℤ` literal arithmetic; with a monic divisor the long
-- division is exact). `ℚ` would get stuck — `Rat` doesn't reduce cheaply in the kernel.
example : (X - 1 : Polynomial ℤ) ∣ (X ^ 2 - 1) := by poly_dvd
theorem dvd_demo : (X + 1 : Polynomial ℤ) ∣ (X ^ 3 + 1) := by poly_dvd
/-- info: 'dvd_demo' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms dvd_demo

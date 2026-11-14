/-
Copyright (c) 2024 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, James Davenport, Michail Karatarakis
-/
import Mathlib.Tactic.ComputablePolynomial.DvdCert

/-!
# Tests for `poly_dvd_cert`

Divisibility of `Polynomial K` by symbolic certificate, over fields, comm rings with monic or
unit-leading-coefficient divisors, with concrete and symbolic coefficients — all axiom-free.
-/

open Polynomial


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

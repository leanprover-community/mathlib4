/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/

import Mathlib.Tactic.Ring.PNat
import Mathlib.Tactic.Ring.RingNF

/-!
# Positive Natural Number Exponentiation for Semigroups

This file defines an exponentiation operation `x ^ n` for semigroups, where `n : ℕ+`.
Unlike monoids where `x ^ 0 = 1` is well-defined, semigroups have no identity element,
so we restrict exponents to positive naturals.

## Main definitions

* `Semigroup.pNatPow` — exponentiation `x ^ n` for `x : S` and `n : ℕ+`.

## Main statements

- `Semigroup.pow_add` — `x ^ m * x ^ n = x ^ (m + n)`.
- `Semigroup.pow_mul` — `(x ^ n) ^ m = x ^ (m * n)`.
- `Semigroup.mul_pow_mul` — `(x * y) ^ n * x = x * (y * x) ^ n`.
- `Monoid.pow_pNat_to_nat` — `x ^ n = x ^ (n : ℕ)` in monoids.
- `WithOne.pow_eq` — `(↑x : WithOne S) ^ n = ↑(x ^ n)`.

## Notation

- `x ^ n` for semigroup powers with `n : ℕ+`.

## Implementation notes

The `@[simp]`-tagged lemmas normalize power expressions. For example,
`(a * b) ^ n * (a * b) ^ m * a ^ 1` normalizes to `a * (b * a) ^ (n + m)`.

## References

Analogous definitions and lemmas for exponentiation in monoids can be found in
`Mathlib.Algebra.Group.Defs`.
-/

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- Exponentiation for semigroups over positive naturals. -/
def pNatPow (x : S) (n : ℕ+) : S :=
  @PNat.recOn n (fun _ => S) x (fun _ ih => ih * x)

instance : Pow S ℕ+ where
  pow := pNatPow

variable (x y : S) (n m : ℕ+)

@[simp] lemma pow_one : x ^ (1 : ℕ+) = x := by
  rfl

@[simp] lemma pow_succ : (x ^ n) * x = x ^ (n + 1) := by
  induction n using PNat.recOn <;> rfl

@[simp] lemma pow_add : x ^ m * x ^ n = x ^ (m + n) := by
  induction n using PNat.recOn with
  | one => rw [pow_one, pow_succ]
  | succ k ih => simp_rw [← add_assoc, ← pow_succ, ← mul_assoc, ih]

@[simp] lemma mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n := by
  induction n using PNat.recOn with
  | one => simp [← mul_assoc]
  | succ n ih => simp only [← pow_succ, ← mul_assoc, ih]

lemma pow_mul_comm : x ^ m * x ^ n = x ^ n * x ^ m := by rw [pow_add, add_comm, pow_add]

lemma pow_mul_comm' : x ^ n * x = x * x ^ n := by
  induction n using PNat.recOn with
  | one    => rfl
  | succ k ih => rw [← pow_succ, ← mul_assoc, ih]

@[simp] lemma pow_mul : (x ^ n) ^ m = x ^ (m * n) := by
  induction m using PNat.recOn with
  | one    => rw [one_mul, pow_one]
  | succ k ih =>
    simp_rw [← pow_succ, ih, pow_add]
    congr
    ring

lemma pow_right_comm : (x ^ m) ^ n = (x ^ n) ^ m := by
  simp only [pow_mul, mul_comm]

end Semigroup

/-- In monoids, `ℕ+` powers agree with `ℕ` powers. -/
lemma Monoid.pow_pNat_to_nat {M} [Monoid M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => simp
  | succ n' ih =>
    rw [PNat.add_coe, PNat.val_ofNat, ← Semigroup.pow_succ, ← Nat.succ_eq_add_one, pow_succ, ih]

/-- Powers in `WithOne S` correspond to embedded powers from `S`. -/
lemma WithOne.pow_eq {S} [Semigroup S] (x : S) (n : ℕ+) : (↑x : WithOne S) ^ n = ↑(x ^ n) := by
  induction n with
  | one => rfl
  | succ n ih => simp_rw [← Semigroup.pow_succ, Semigroup.pow_mul_comm', WithOne.coe_mul, ih]

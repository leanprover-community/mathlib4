/-
Copyright (c) 2026 The Mathlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Hart-Hodgson, Ayden Lamparski, Soleil Repple, Howard Straubing
-/
module

public import Mathlib.Data.PNat.Basic

/-!
# Positive Natural Number Exponentiation for Semigroups

This file defines an exponentiation operation `x ^ n` for semigroups, where `n : ℕ+`.
Unlike monoids where `x ^ 0 = 1` is well-defined, semigroups have no identity element,
so we restrict exponents to positive naturals.

## Main definitions

* `Semigroup.pNatPow` — exponentiation `x ^ n` for `x : S` and `n : ℕ+`.

## Main statements

- `Semigroup.pow_add` — `x ^ (m + n) = x ^ m * x ^ n`.
- `Semigroup.pow_mul` — `x ^ (m * n) = (x ^ n) ^ m`.
- `Semigroup.mul_pow_mul` — `(x * y) ^ n * x = x * (y * x) ^ n`.
- `Monoid.pow_pNat_to_nat` — `x ^ n = x ^ (n : ℕ)` in monoids.
- `WithOne.pow_eq` — `(↑x : WithOne S) ^ n = ↑(x ^ n)`.

## Notation

- `x ^ n` for semigroup powers with `n : ℕ+`.

## References

Analogous definitions and lemmas for exponentiation in monoids can be found in
`Mathlib.Algebra.Group.Defs`.
-/

@[expose] public section

namespace Semigroup

variable {S : Type*} [Semigroup S]

/-- Exponentiation for semigroups over positive naturals. -/
instance : Pow S ℕ+ where
  pow x n := PNat.recOn n x (fun _ ih => ih * x)

variable (x y : S) (n m : ℕ+)

@[simp] lemma pow_one : x ^ (1 : ℕ+) = x := by rfl

lemma pow_succ : x ^ (n + 1) = (x ^ n) * x := by
  induction n using PNat.recOn <;> rfl

lemma pow_succ' : x ^ (n + 1) = x * (x ^ n) := by
  induction n using PNat.recOn with
  | one => rfl
  | succ n ih =>
    nth_rw 2 [pow_succ]
    rw [← mul_assoc, ← ih, pow_succ]

@[simp] lemma pow_add : x ^ (m + n) = x ^ m * x ^ n := by
  induction n using PNat.recOn with
  | one => rw [pow_one, pow_succ]
  | succ n ih => simp_rw [← add_assoc, pow_succ, ← mul_assoc, ih]

lemma mul_pow_mul : (x * y) ^ n * x = x * (y * x) ^ n := by
  induction n using PNat.recOn with
  | one => simp [← mul_assoc]
  | succ n ih => simp only [pow_succ, ← mul_assoc, ih]

lemma pow_mul_comm : x ^ m * x ^ n = x ^ n * x ^ m := by
  rw [← pow_add, add_comm, pow_add]

lemma pow_mul_comm' : x ^ n * x = x * x ^ n := by
  induction n using PNat.recOn with
  | one => rfl
  | succ n ih => rw [pow_succ, ← mul_assoc, ih]

lemma pow_mul : x ^ (m * n) = (x ^ n) ^ m := by
  induction m using PNat.recOn with
  | one => rw [one_mul, pow_one]
  | succ k ih => rw [pow_succ, ← ih, ← pow_add, add_one_mul]

lemma pow_mul' : x ^ (m * n) = (x ^ m) ^ n := by
  induction n using PNat.recOn with
  | one => rw [mul_one, pow_one]
  | succ k ih => rw [pow_succ, ← ih, ← pow_add, mul_add_one]

lemma pow_right_comm : (x ^ m) ^ n = (x ^ n) ^ m := by
  simp_rw [← pow_mul, mul_comm]

end Semigroup

/-- In monoids, `ℕ+` powers agree with `ℕ` powers. -/
lemma Monoid.pow_pNat_to_nat {M} [Monoid M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => simp
  | succ n' ih =>
    rw [PNat.add_coe, PNat.val_ofNat, Semigroup.pow_succ, ← Nat.succ_eq_add_one, pow_succ, ih]

/-- Powers in `WithOne S` correspond to embedded powers from `S`. -/
lemma WithOne.pow_eq {S} [Semigroup S] (x : S) (n : ℕ+) : (↑x : WithOne S) ^ n = ↑(x ^ n) := by
  induction n with
  | one => rfl
  | succ n ih => simp_rw [Semigroup.pow_succ, Semigroup.pow_mul_comm', WithOne.coe_mul, ih]

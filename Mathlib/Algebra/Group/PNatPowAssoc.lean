/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/

import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupPower.Basic
import Mathlib.Data.PNat.Basic

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `PNatPowAssoc`, where `PNat` means only strictly positive
powers are considered.

## Results

- `ppow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `ppow_one` a defining property: `x ^ 1 = x`
- `ppow_assoc` strictly positive powers of an element have associative multiplication.
- `ppow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `ppow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `ppow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

- `Pow M ℕ+` for semigroups `M`.
- `PNatPowAssoc` for semigroups.

## Todo

* `NatPowAssoc` for `MulOneClass` - more or less the same flow
* It seems unlikely that anyone will want `NatSMulAssoc` and `PNatSmulAssoc` as additive versions of
  power-associativity, but we have found that it is not hard to write.

-/

universe u

variable {M : Type u}

section PNatPowAssoc

variable [Mul M] [Pow M ℕ+]

/-- A `Prop`-valued mixin for power-associative multiplication in the non-unital setting. -/
class PNatPowAssoc (M : Type u) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : ∀ (k n : ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x

theorem ppow_add [PNatPowAssoc M] (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

@[simp]
theorem ppow_one [PNatPowAssoc M] (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x

theorem ppow_assoc [PNatPowAssoc M] (k m n : ℕ+) (x : M) :
    x ^ k * (x ^ m * x ^ n) = (x ^ k * x ^ m) * x ^ n := by
  simp only [← ppow_add, add_assoc]

theorem ppow_comm [PNatPowAssoc M] (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

theorem ppow_mul [PNatPowAssoc M] (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  refine PNat.recOn n ?_ ?_
  rw [ppow_one, mul_one]
  intro k hk
  rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

end PNatPowAssoc

theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  refine PNat.recOn n ?_ ?_
  rw [ppow_one, PNat.one_coe, pow_one]
  intro k hk
  rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

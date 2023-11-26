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

section ppowRec

variable [Mul M]

/-- A strictly positive integer power operation. `ppowRec n a = a * (a * (⋯ * a) ⋯ )` n times. -/
def ppowRec : ℕ+ → M → M :=
  fun n => PNat.recOn n (fun x ↦ x) (fun _ y => fun x => x * y x)

@[simp]
theorem ppowRec_one (x : M) : ppowRec 1 x = x := rfl

theorem ppowRec_succ (x : M) (n : ℕ+) : ppowRec (n + 1) x = x * ppowRec n x := by
  refine PNat.recOn n rfl ?_
  intro k _
  exact rfl

end ppowRec

section Semigroup

variable [Semigroup M]

namespace Semigroup

instance (M: Type u) [Semigroup M] : Pow M ℕ+ :=
  {
    pow := fun x n => ppowRec n x
  }

theorem ppow_eq_ppowRec (x : M) (n : ℕ+) : x ^ n = ppowRec n x := rfl

theorem ppow_add (x : M) (k n : ℕ+) : x ^ (k + n) = x ^ k * x ^ n := by
  simp only [ppow_eq_ppowRec]
  refine PNat.recOn k ?_ ?_
  rw [add_comm, ppowRec_one, ppowRec_succ]
  intro k hk
  rw [ppowRec_succ, mul_assoc, ← hk, ← ppowRec_succ, add_right_comm]

instance (M: Type u) [Semigroup M] : PNatPowAssoc M :=
  {
    ppow_add := fun k n x => ppow_add x k n
    ppow_one := ppowRec_one
  }

end Semigroup

end Semigroup

theorem ppow_eq_pow [Monoid M] (x : M) (n : ℕ+) : x ^ n = x ^ (n : ℕ) := by
  refine PNat.recOn n ?_ ?_
  rw [Semigroup.ppow_eq_ppowRec, ppowRec_one, PNat.one_coe, pow_one]
  intro k hk
  rw [Semigroup.ppow_eq_ppowRec, ppowRec_succ, PNat.add_coe, add_comm, pow_add, PNat.one_coe, ← hk,
    pow_one, Semigroup.ppow_eq_ppowRec]

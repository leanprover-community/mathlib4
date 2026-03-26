/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
module

public import Mathlib.Data.PNat.Basic
public import Mathlib.Algebra.Notation.Prod

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

- PNatPowAssoc for products and Pi types

## TODO

* `NatPowAssoc` for `MulOneClass` - more or less the same flow
* It seems unlikely that anyone will want `NatSMulAssoc` and `PNatSMulAssoc` as additive versions of
  power-associativity, but we have found that it is not hard to write.

-/

@[expose] public section

-- TODO:
-- assert_not_exists MonoidWithZero

variable {M : Type*}

/-- A `Prop`-valued mixin for power-associative multiplication in the non-unital setting. -/
class PNatPowAssoc (M : Type*) [Mul M] [Pow M ℕ+] : Prop where
  /-- Multiplication is power-associative. -/
  protected ppow_add : ∀ (k n : ℕ+) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent one is identity. -/
  protected ppow_one : ∀ (x : M), x ^ (1 : ℕ+) = x

section Mul

variable [Mul M] [Pow M ℕ+] [PNatPowAssoc M]

theorem ppow_add (k n : ℕ+) (x : M) : x ^ (k + n) = x ^ k * x ^ n :=
  PNatPowAssoc.ppow_add k n x

@[simp]
theorem ppow_one (x : M) : x ^ (1 : ℕ+) = x :=
  PNatPowAssoc.ppow_one x

set_option backward.isDefEq.respectTransparency false in
theorem ppow_mul_assoc (k m n : ℕ+) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← ppow_add, add_assoc]

set_option backward.isDefEq.respectTransparency false in
theorem ppow_mul_comm (m n : ℕ+) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← ppow_add, add_comm]

set_option backward.isDefEq.respectTransparency false in
theorem ppow_mul (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | one => rw [ppow_one, mul_one]
  | succ k hk => rw [ppow_add, ppow_one, mul_add, ppow_add, mul_one, hk]

set_option backward.isDefEq.respectTransparency false in
theorem ppow_mul' (x : M) (m n : ℕ+) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact ppow_mul x n m

end Mul

instance Pi.instPNatPowAssoc {ι : Type*} {α : ι → Type*} [∀ i, Mul <| α i] [∀ i, Pow (α i) ℕ+]
    [∀ i, PNatPowAssoc <| α i] : PNatPowAssoc (∀ i, α i) where
  ppow_add _ _ _ := by ext; simp [ppow_add]
  ppow_one _ := by ext; simp

instance Prod.instPNatPowAssoc {N : Type*} [Mul M] [Pow M ℕ+] [PNatPowAssoc M] [Mul N] [Pow N ℕ+]
    [PNatPowAssoc N] : PNatPowAssoc (M × N) where
  ppow_add _ _ _ := by ext <;> simp [ppow_add]
  ppow_one _ := by ext <;> simp

theorem ppow_eq_pow [Monoid M] [Pow M ℕ+] [PNatPowAssoc M] (x : M) (n : ℕ+) :
    x ^ n = x ^ (n : ℕ) := by
  induction n with
  | one => rw [ppow_one, PNat.one_coe, pow_one]
  | succ k hk => rw [ppow_add, ppow_one, PNat.add_coe, pow_add, PNat.one_coe, pow_one, ← hk]

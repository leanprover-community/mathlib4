/-
Copyright (c) 2023 Scott Carnahan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Carnahan
-/
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Algebra.Group.Prod

/-!
# Typeclasses for power-associative structures

In this file we define power-associativity for algebraic structures with a multiplication operation.
The class is a Prop-valued mixin named `NatPowAssoc`.

## Results

- `npow_add` a defining property: `x ^ (k + n) = x ^ k * x ^ n`
- `npow_one` a defining property: `x ^ 1 = x`
- `npow_assoc` strictly positive powers of an element have associative multiplication.
- `npow_comm` `x ^ m * x ^ n = x ^ n * x ^ m` for strictly positive `m` and `n`.
- `npow_mul` `x ^ (m * n) = (x ^ m) ^ n` for strictly positive `m` and `n`.
- `npow_eq_pow` monoid exponentiation coincides with semigroup exponentiation.

## Instances

We also produce the following instances:

- `NatPowAssoc` for Monoids, Pi types and products.

## TODO

* to_additive?

-/

assert_not_exists DenselyOrdered

variable {M : Type*}

/-- A mixin for power-associative multiplication. -/
class NatPowAssoc (M : Type*) [MulOneClass M] [Pow M ℕ] : Prop where
  /-- Multiplication is power-associative. -/
  protected npow_add : ∀ (k n : ℕ) (x : M), x ^ (k + n) = x ^ k * x ^ n
  /-- Exponent zero is one. -/
  protected npow_zero : ∀ (x : M), x ^ 0 = 1
  /-- Exponent one is identity. -/
  protected npow_one : ∀ (x : M), x ^ 1 = x

section MulOneClass

variable [MulOneClass M] [Pow M ℕ] [NatPowAssoc M]

theorem npow_add (k n : ℕ) (x : M) : x ^ (k + n) = x ^ k * x ^ n  :=
  NatPowAssoc.npow_add k n x

@[simp]
theorem npow_zero (x : M) : x ^ 0 = 1 :=
  NatPowAssoc.npow_zero x

@[simp]
theorem npow_one (x : M) : x ^ 1 = x :=
  NatPowAssoc.npow_one x

theorem npow_mul_assoc (k m n : ℕ) (x : M) :
    (x ^ k * x ^ m) * x ^ n = x ^ k * (x ^ m * x ^ n) := by
  simp only [← npow_add, add_assoc]

theorem npow_mul_comm (m n : ℕ) (x : M) :
    x ^ m * x ^ n = x ^ n * x ^ m := by simp only [← npow_add, add_comm]

theorem npow_mul (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ m) ^ n := by
  induction n with
  | zero => rw [npow_zero, Nat.mul_zero, npow_zero]
  | succ n ih => rw [mul_add, npow_add, ih, mul_one, npow_add, npow_one]

theorem npow_mul' (x : M) (m n : ℕ) : x ^ (m * n) = (x ^ n) ^ m := by
  rw [mul_comm]
  exact npow_mul x n m

end MulOneClass

section Neg

theorem neg_npow_assoc {R : Type*} [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R] (a b : R) (k : ℕ) :
    (-1)^k * a * b = (-1)^k * (a * b) := by
  induction k with
  | zero => simp only [npow_zero, one_mul]
  | succ k ih =>
    rw [npow_add, npow_one, ← neg_mul_comm, mul_one]
    simp only [neg_mul, ih]

end Neg

instance Pi.instNatPowAssoc {ι : Type*} {α : ι → Type*} [∀ i, MulOneClass <| α i] [∀ i, Pow (α i) ℕ]
    [∀ i, NatPowAssoc <| α i] : NatPowAssoc (∀ i, α i) where
    npow_add _ _ _ := by ext; simp [npow_add]
    npow_zero _ := by ext; simp
    npow_one _ := by ext; simp

instance Prod.instNatPowAssoc {N : Type*} [MulOneClass M] [Pow M ℕ] [NatPowAssoc M] [MulOneClass N]
    [Pow N ℕ] [NatPowAssoc N] : NatPowAssoc (M × N) where
  npow_add _ _ _ := by ext <;> simp [npow_add]
  npow_zero _ := by ext <;> simp
  npow_one _ := by ext <;> simp

section Monoid

variable [Monoid M]

instance Monoid.PowAssoc : NatPowAssoc M where
  npow_add _ _ _ := pow_add _ _ _
  npow_zero _ := pow_zero _
  npow_one _ := pow_one _

@[simp, norm_cast]
theorem Nat.cast_npow (R : Type*) [NonAssocSemiring R] [Pow R ℕ] [NatPowAssoc R] (n m : ℕ) :
    (↑(n ^ m) : R) = (↑n : R) ^ m := by
  induction m with
  | zero => simp only [pow_zero, Nat.cast_one, npow_zero]
  | succ m ih => rw [npow_add, npow_add, Nat.cast_mul, ih, npow_one, npow_one]

@[simp, norm_cast]
theorem Int.cast_npow (R : Type*) [NonAssocRing R] [Pow R ℕ] [NatPowAssoc R]
    (n : ℤ) : ∀(m : ℕ), @Int.cast R NonAssocRing.toIntCast (n ^ m) = (n : R) ^ m
  | 0 => by
    rw [pow_zero, npow_zero, Int.cast_one]
  | m + 1 => by
    rw [npow_add, npow_one, Int.cast_mul, Int.cast_npow R n m, npow_add, npow_one]

end Monoid

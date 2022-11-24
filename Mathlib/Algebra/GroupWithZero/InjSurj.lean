/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.GroupWithZero.Defs

/-!
# Lifting groups with zero along injective/surjective maps

-/


open Function

variable {M₀ G₀ M₀' G₀' : Type _}

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/-- Pullback a `mul_zero_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0)
    (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  zero_mul a := hf <| by simp only [mul, zero, zero_mul]
  mul_zero a := hf <| by simp only [mul, zero, mul_zero]
#align function.injective.mul_zero_class Function.Injective.mulZeroClass

/-- Pushforward a `mul_zero_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0)
    (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]
#align function.surjective.mul_zero_class Function.Surjective.mulZeroClass

end MulZeroClass

section NoZeroDivisors

/-- Pushforward a `no_zero_divisors` instance along an injective function. -/
protected theorem Function.Injective.no_zero_divisors [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀'] [NoZeroDivisors M₀']
    (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : NoZeroDivisors M₀ :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun x y H =>
      have : f x * f y = 0 := by rw [← mul, H, zero]
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp (fun H => hf <| by rwa [zero]) fun H => hf <| by rwa [zero] }
#align function.injective.no_zero_divisors Function.Injective.no_zero_divisors

end NoZeroDivisors

section MulZeroOneClass

variable [MulZeroOneClass M₀]

/-- Pullback a `mul_zero_one_class` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀) (hf : Injective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroOneClass M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }
#align function.injective.mul_zero_one_class Function.Injective.mulZeroOneClass

/-- Pushforward a `mul_zero_one_class` instance along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroOneClass M₀' :=
  { hf.MulZeroClass f zero mul, hf.MulOneClass f one mul with }
#align function.surjective.mul_zero_one_class Function.Surjective.mulZeroOneClass

end MulZeroOneClass

section SemigroupWithZero

/-- Pullback a `semigroup_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : SemigroupWithZero M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }
#align function.injective.semigroup_with_zero Function.Injective.semigroupWithZero

/-- Pushforward a `semigroup_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) : SemigroupWithZero M₀' :=
  { hf.MulZeroClass f zero mul, ‹Zero M₀'›, hf.Semigroup f mul with }
#align function.surjective.semigroup_with_zero Function.Surjective.semigroupWithZero

end SemigroupWithZero

section MonoidWithZero

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [MonoidWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : MonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.injective.monoid_with_zero Function.Injective.monoidWithZero

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [MonoidWithZero M₀]
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : MonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.surjective.monoid_with_zero Function.Surjective.monoidWithZero

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [CommMonoidWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.injective.comm_monoid_with_zero Function.Injective.commMonoidWithZero

/-- Pushforward a `monoid_with_zero` class along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] [CommMonoidWithZero M₀]
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CommMonoidWithZero M₀' :=
  { hf.CommMonoid f one mul npow, hf.MulZeroClass f zero mul with }
#align function.surjective.comm_monoid_with_zero Function.Surjective.commMonoidWithZero

end MonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

/-- Pullback a `monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelMonoidWithZero M₀' :=
  { hf.Monoid f one mul npow, hf.MulZeroClass f zero mul with
    mul_left_cancel_of_ne_zero := fun x y z hx H =>
      hf <| mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] <;> rfl,
    mul_right_cancel_of_ne_zero := fun x y z hx H =>
      hf <| mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] <;> rfl }
#align function.injective.cancel_monoid_with_zero Function.Injective.cancelMonoidWithZero

end CancelMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M₀] {a b c : M₀}

/-- Pullback a `cancel_comm_monoid_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelCommMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) : CancelCommMonoidWithZero M₀' :=
  { hf.CommMonoidWithZero f zero one mul npow, hf.CancelMonoidWithZero f zero one mul npow with }
#align function.injective.cancel_comm_monoid_with_zero Function.Injective.cancelCommMonoidWithZero

end CancelCommMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

/-- Pullback a `group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow, pullback_nonzero f zero one with
    inv_zero := hf <| by erw [inv, zero, inv_zero],
    mul_inv_cancel := fun x hx => hf <| by erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)] }
#align function.injective.group_with_zero Function.Injective.groupWithZero

/-- Pushforward a `group_with_zero` class along an surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.MonoidWithZero f zero one mul npow, hf.DivInvMonoid f one mul inv div npow zpow with
    inv_zero := by erw [← zero, ← inv, inv_zero],
    mul_inv_cancel :=
      hf.forall.2 fun x hx => by
        erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) <| trans_rel_left Ne hx zero.symm)] <;> exact one,
    exists_pair_ne := ⟨0, 1, h01⟩ }
#align function.surjective.group_with_zero Function.Surjective.groupWithZero

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

/-- Pullback a `comm_group_with_zero` class along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }
#align function.injective.comm_group_with_zero Function.Injective.commGroupWithZero

/-- Pushforward a `comm_group_with_zero` class along a surjective function. -/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀'] [Pow G₀' ℕ]
    [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.GroupWithZero h01 f zero one mul inv div npow zpow, hf.CommSemigroup f mul with }
#align function.surjective.comm_group_with_zero Function.Surjective.commGroupWithZero

end CommGroupWithZero

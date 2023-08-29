/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Algebra.Group.InjSurj
import Mathlib.Algebra.GroupWithZero.Defs

#align_import algebra.group_with_zero.inj_surj from "leanprover-community/mathlib"@"a148d797a1094ab554ad4183a4ad6f130358ef64"

/-!
# Lifting groups with zero along injective/surjective maps

-/


open Function

variable {M₀ G₀ M₀' G₀' : Type*}

section MulZeroClass

variable [MulZeroClass M₀] {a b : M₀}

/-- Pull back a `MulZeroClass` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀' → M₀) (hf : Injective f)
    (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) : MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  zero_mul a := hf <| by simp only [mul, zero, zero_mul]
                         -- 🎉 no goals
  mul_zero a := hf <| by simp only [mul, zero, mul_zero]
                         -- 🎉 no goals
#align function.injective.mul_zero_class Function.Injective.mulZeroClass

/-- Push forward a `MulZeroClass` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroClass [Mul M₀'] [Zero M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroClass M₀' where
  mul := (· * ·)
  zero := 0
  mul_zero := hf.forall.2 fun x => by simp only [← zero, ← mul, mul_zero]
                                      -- 🎉 no goals
                                      -- 🎉 no goals
  zero_mul := hf.forall.2 fun x => by simp only [← zero, ← mul, zero_mul]
#align function.surjective.mul_zero_class Function.Surjective.mulZeroClass

end MulZeroClass

section NoZeroDivisors

variable [Mul M₀] [Zero M₀] [Mul M₀'] [Zero M₀']
  (f : M₀ → M₀') (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y)

/-- Pull back a `NoZeroDivisors` instance along an injective function. -/
protected theorem Function.Injective.noZeroDivisors [NoZeroDivisors M₀'] : NoZeroDivisors M₀ :=
  { eq_zero_or_eq_zero_of_mul_eq_zero := fun H =>
      have : f _ * f _ = 0 := by rw [← mul, H, zero]
                                 -- 🎉 no goals
      (eq_zero_or_eq_zero_of_mul_eq_zero this).imp
        (fun H => hf <| by rwa [zero]) fun H => hf <| by rwa [zero] }
                           -- 🎉 no goals
                                                         -- 🎉 no goals
#align function.injective.no_zero_divisors Function.Injective.noZeroDivisors

protected theorem Function.Injective.isLeftCancelMulZero
    [IsLeftCancelMulZero M₀'] : IsLeftCancelMulZero M₀ :=
  { mul_left_cancel_of_ne_zero := fun Hne He => by
      have := congr_arg f He
      -- ⊢ b✝ = c✝
      rw [mul, mul] at this
      -- ⊢ b✝ = c✝
      exact hf (mul_left_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this) }
      -- 🎉 no goals

protected theorem Function.Injective.isRightCancelMulZero
    [IsRightCancelMulZero M₀'] : IsRightCancelMulZero M₀ :=
  { mul_right_cancel_of_ne_zero := fun Hne He => by
      have := congr_arg f He
      -- ⊢ a✝ = c✝
      rw [mul, mul] at this
      -- ⊢ a✝ = c✝
      exact hf (mul_right_cancel₀ (fun Hfa => Hne <| hf <| by rw [Hfa, zero]) this) }
      -- 🎉 no goals

end NoZeroDivisors

section MulZeroOneClass

variable [MulZeroOneClass M₀]

/-- Pull back a `MulZeroOneClass` instance along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀' → M₀)
    (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }
#align function.injective.mul_zero_one_class Function.Injective.mulZeroOneClass

/-- Push forward a `MulZeroOneClass` instance along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.mulZeroOneClass [Mul M₀'] [Zero M₀'] [One M₀'] (f : M₀ → M₀')
    (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ a b, f (a * b) = f a * f b) :
    MulZeroOneClass M₀' :=
  { hf.mulZeroClass f zero mul, hf.mulOneClass f one mul with }
#align function.surjective.mul_zero_one_class Function.Surjective.mulZeroOneClass

end MulZeroOneClass

section SemigroupWithZero

/-- Pull back a `SemigroupWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.semigroupWithZero [Zero M₀'] [Mul M₀'] [SemigroupWithZero M₀]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }
#align function.injective.semigroup_with_zero Function.Injective.semigroupWithZero

/-- Push forward a `SemigroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.semigroupWithZero [SemigroupWithZero M₀] [Zero M₀'] [Mul M₀']
    (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (mul : ∀ x y, f (x * y) = f x * f y) :
    SemigroupWithZero M₀' :=
  { hf.mulZeroClass f zero mul, ‹Zero M₀'›, hf.semigroup f mul with }
#align function.surjective.semigroup_with_zero Function.Surjective.semigroupWithZero

end SemigroupWithZero

section MonoidWithZero

/-- Pull back a `MonoidWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }
#align function.injective.monoid_with_zero Function.Injective.monoidWithZero

/-- Push forward a `MonoidWithZero` along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.monoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [MonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    MonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with }
#align function.surjective.monoid_with_zero Function.Surjective.monoidWithZero

/-- Pull back a `CommMonoidWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }
#align function.injective.comm_monoid_with_zero Function.Injective.commMonoidWithZero

/-- Push forward a `CommMonoidWithZero` along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.commMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    [CommMonoidWithZero M₀] (f : M₀ → M₀') (hf : Surjective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CommMonoidWithZero M₀' :=
  { hf.commMonoid f one mul npow, hf.mulZeroClass f zero mul with }
#align function.surjective.comm_monoid_with_zero Function.Surjective.commMonoidWithZero

end MonoidWithZero

section CancelMonoidWithZero

variable [CancelMonoidWithZero M₀] {a b c : M₀}

/-- Pull back a `CancelMonoidWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelMonoidWithZero M₀' :=
  { hf.monoid f one mul npow, hf.mulZeroClass f zero mul with
    mul_left_cancel_of_ne_zero := fun hx H =>
      hf <| mul_left_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H],
                                                            -- 🎉 no goals
    mul_right_cancel_of_ne_zero := fun hx H =>
      hf <| mul_right_cancel₀ ((hf.ne_iff' zero).2 hx) <| by erw [← mul, ← mul, H] }
                                                             -- 🎉 no goals
#align function.injective.cancel_monoid_with_zero Function.Injective.cancelMonoidWithZero

end CancelMonoidWithZero

section CancelCommMonoidWithZero

variable [CancelCommMonoidWithZero M₀] {a b c : M₀}

/-- Pull back a `CancelCommMonoidWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.cancelCommMonoidWithZero [Zero M₀'] [Mul M₀'] [One M₀'] [Pow M₀' ℕ]
    (f : M₀' → M₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) :
    CancelCommMonoidWithZero M₀' :=
  { hf.commMonoidWithZero f zero one mul npow, hf.cancelMonoidWithZero f zero one mul npow with }
#align function.injective.cancel_comm_monoid_with_zero Function.Injective.cancelCommMonoidWithZero

end CancelCommMonoidWithZero

section GroupWithZero

variable [GroupWithZero G₀] {a b c g h x : G₀}

/-- Pull back a `GroupWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0) (one : f 1 = 1)
    (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow,
    hf.divInvMonoid f one mul inv div npow zpow,
    pullback_nonzero f zero one with
    inv_zero := hf <| by erw [inv, zero, inv_zero],
                         -- 🎉 no goals
    mul_inv_cancel := fun x hx => hf <| by
      erw [one, mul, inv, mul_inv_cancel ((hf.ne_iff' zero).2 hx)] }
      -- 🎉 no goals
#align function.injective.group_with_zero Function.Injective.groupWithZero

/-- Push forward a `GroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Surjective.groupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀'] [Div G₀']
    [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    GroupWithZero G₀' :=
  { hf.monoidWithZero f zero one mul npow, hf.divInvMonoid f one mul inv div npow zpow with
    inv_zero := by erw [← zero, ← inv, inv_zero],
                   -- 🎉 no goals
    mul_inv_cancel := hf.forall.2 fun x hx => by
        erw [← inv, ← mul, mul_inv_cancel (mt (congr_arg f) <| fun h ↦ hx (h.trans zero)), one]
        -- 🎉 no goals
    exists_pair_ne := ⟨0, 1, h01⟩ }
#align function.surjective.group_with_zero Function.Surjective.groupWithZero

end GroupWithZero

section CommGroupWithZero

variable [CommGroupWithZero G₀] {a b c d : G₀}

/-- Pull back a `CommGroupWithZero` along an injective function.
See note [reducible non-instances]. -/
@[reducible]
protected def Function.Injective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (f : G₀' → G₀) (hf : Injective f) (zero : f 0 = 0)
    (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y) (inv : ∀ x, f x⁻¹ = (f x)⁻¹)
    (div : ∀ x y, f (x / y) = f x / f y) (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n)
    (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) : CommGroupWithZero G₀' :=
  { hf.groupWithZero f zero one mul inv div npow zpow, hf.commSemigroup f mul with }
#align function.injective.comm_group_with_zero Function.Injective.commGroupWithZero

/-- Push forward a `CommGroupWithZero` along a surjective function.
See note [reducible non-instances]. -/
protected def Function.Surjective.commGroupWithZero [Zero G₀'] [Mul G₀'] [One G₀'] [Inv G₀']
    [Div G₀'] [Pow G₀' ℕ] [Pow G₀' ℤ] (h01 : (0 : G₀') ≠ 1) (f : G₀ → G₀') (hf : Surjective f)
    (zero : f 0 = 0) (one : f 1 = 1) (mul : ∀ x y, f (x * y) = f x * f y)
    (inv : ∀ x, f x⁻¹ = (f x)⁻¹) (div : ∀ x y, f (x / y) = f x / f y)
    (npow : ∀ (x) (n : ℕ), f (x ^ n) = f x ^ n) (zpow : ∀ (x) (n : ℤ), f (x ^ n) = f x ^ n) :
    CommGroupWithZero G₀' :=
  { hf.groupWithZero h01 f zero one mul inv div npow zpow, hf.commSemigroup f mul with }
#align function.surjective.comm_group_with_zero Function.Surjective.commGroupWithZero

end CommGroupWithZero

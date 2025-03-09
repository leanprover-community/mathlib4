/-
Copyright (c) 2025 Aaron Liu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Liu
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Group.Pi.Basic

/-!
# FunLike

This file defines typeclasses for `FunLike`s with monoid structures.
For these `FunLike`s, the coercion to a function can be seen as a monoid homomorphism.

* `ZeroFunLike`
* `AddFunLike`
* `AddMonoidFunLike`

* `OneFunLike`
* `MulFunLike`
* `MonoidFunLike`
-/

variable {α : Type*} {β : α → Type*} {F : Type*} [DFunLike F α β]

section Zero

variable (F) in
/-- `ZeroFunLike F` states that `0 a = 0`. -/
class ZeroFunLike [∀ a, Zero (β a)] [Zero F] where
  protected zero_map' : ∀ a, (0 : F) a = 0

end Zero

section Add

variable (F) in
/-- `AddFunLike F` states that `(f + g) a = f a + g a`. -/
class AddFunLike [∀ a, Add (β a)] [Add F] where
  protected add_map' : ∀ f g a, (f + g : F) a = f a + g a

end Add

section add_zero

variable (F) in
/-- `AddMonoidFunLike F` states that `(⇑)` is a monoid homomorphism. -/
class AddMonoidFunLike [∀ a, AddZeroClass (β a)] [AddZeroClass F] extends
  ZeroFunLike F, AddFunLike F

end add_zero

section One

variable (F) in
/-- `OneFunLike F` states that `1 a = 1`. -/
@[to_additive]
class OneFunLike [∀ a, One (β a)] [One F] where
  protected one_map' : ∀ a, (1 : F) a = 1

end One

section Add

variable (F) in
/-- `MulFunLike F` states that `(f * g) a = f a * g a`. -/
@[to_additive]
class MulFunLike [∀ a, Mul (β a)] [Mul F] where
  protected mul_map' : ∀ f g a, (f * g : F) a = f a * g a

end Add

section add_zero

variable (F) in
/-- `MonoidFunLike F` states that `(⇑)` is a monoid homomorphism. -/
@[to_additive]
class MonoidFunLike [∀ a, MulOneClass (β a)] [MulOneClass F] extends
  OneFunLike F, MulFunLike F

end add_zero

@[to_additive (attr := simp)]
theorem one_map [∀ a, One (β a)] [One F] [OneFunLike F] (a : α) :
    (1 : F) a = 1 := OneFunLike.one_map' a

@[to_additive (attr := simp)]
theorem mul_map [∀ a, Mul (β a)] [Mul F] [MulFunLike F] (f g : F) (a : α) :
    ⇑(f * g) a = f a * g a := MulFunLike.mul_map' f g a

namespace DFunLike

@[to_additive (attr := simp, norm_cast)]
theorem coe_one [∀ a, One (β a)] [One F] [OneFunLike F] :
    ⇑(1 : F) = 1 := funext one_map

@[to_additive (attr := simp, norm_cast)]
theorem coe_mul [∀ a, Mul (β a)] [Mul F] [MulFunLike F] (f g : F) :
    ⇑(f * g : F) = f * g := funext (mul_map f g)

/-- `DFunLike.coe`, as a `OneHom`. -/
@[to_additive (attr := simps) "`DFunLike.coe`, as a `ZeroHom`."]
def coeOneHom [∀ a, One (β a)] [One F] [OneFunLike F] : OneHom F ((a : α) → β a) where
  toFun := coe
  map_one' := coe_one

/-- Application at `a`, as a `OneHom`. -/
@[to_additive (attr := simps) "Application at `a`, as a `ZeroHom`."]
def applyOneHom [∀ a, One (β a)] [One F] [OneFunLike F] (a : α) : OneHom F (β a) where
  toFun f := f a
  map_one' := one_map a

/-- `DFunLike.coe`, as a `MulHom`. -/
@[to_additive (attr := simps) "`DFunLike.coe`, as an `AddHom`."]
def coeMulHom [∀ a, Mul (β a)] [Mul F] [MulFunLike F] : F →ₙ* ((a : α) → β a) where
  toFun := coe
  map_mul' := coe_mul

/-- Application at `a`, as a `MulHom`. -/
@[to_additive (attr := simps) "Application at `a`, as an `AddHom`."]
def applyMulHom [∀ a, Mul (β a)] [Mul F] [MulFunLike F] (a : α) : F →ₙ* (β a) where
  toFun f := f a
  map_mul' f g := mul_map f g a

/-- `DFunLike.coe`, as a `MonoidHom`. -/
@[to_additive (attr := simps) "`DFunLike.coe`, as an `AddMonoidHom`."]
def coeMonoidHom [∀ a, MulOneClass (β a)] [MulOneClass F] [MonoidFunLike F] :
    F →* ((a : α) → β a) where
  toFun := coe
  map_one' := coe_one
  map_mul' := coe_mul

/-- Application at `a`, as a `MonoidHom`. -/
@[to_additive (attr := simps) "Application at `a`, as an `AddMonoidHom`."]
def applyMonoidHom [∀ a, MulOneClass (β a)] [MulOneClass F] [MonoidFunLike F]
    (a : α) : F →* (β a) where
  toFun f := f a
  map_one' := one_map a
  map_mul' f g := mul_map f g a

end DFunLike

namespace DFunLike

@[to_additive]
theorem coe_mul_eq_one [∀ a, MulOneClass (β a)] [MulOneClass F] [MonoidFunLike F]
    {f g : F} (h : f * g = 1) : ⇑f * ⇑g = 1 :=
  map_mul_eq_one coeMonoidHom h

@[to_additive]
theorem coe_div' [∀ a, DivInvMonoid (β a)] [DivInvMonoid F] [MulFunLike F]
    (h : ∀ (f : F), ⇑f⁻¹ = (⇑f)⁻¹) (f g : F) : ⇑(f / g) = ⇑f / ⇑g :=
  map_div' coeMulHom h f g

@[to_additive (attr := simp low, norm_cast)]
theorem coe_inv [∀ a, DivisionMonoid (β a)] [Group F] [MonoidFunLike F]
    (f : F) : ⇑f⁻¹ = (⇑f)⁻¹ :=
  map_inv coeMonoidHom f

@[to_additive (attr := simp low, norm_cast)]
theorem coe_div [∀ a, DivisionMonoid (β a)] [Group F] [MonoidFunLike F]
    (f g : F) : ⇑(f / g) = ⇑f / ⇑g :=
  map_div coeMonoidHom f g

@[to_additive (attr := simp low, norm_cast) (reorder := 8 9)]
theorem coe_pow [∀ a, Monoid (β a)] [Monoid F] [MonoidFunLike F] (f : F) (n : ℕ) :
    ⇑(f ^ n) = ⇑f ^ n :=
  map_pow coeMonoidHom f n

@[to_additive]
theorem coe_zpow' [∀ a, DivInvMonoid (β a)] [DivInvMonoid F] [MonoidFunLike F]
    (h : ∀ (f : F), ⇑f⁻¹ = (⇑f)⁻¹) (f : F) (n : ℤ) : ⇑(f ^ n) = ⇑f ^ n :=
  map_zpow' coeMonoidHom h f n

@[to_additive (attr := simp low, norm_cast) (reorder := 8 9)]
theorem coe_zpow [∀ a, DivisionMonoid (β a)] [Group F] [MonoidFunLike F]
    (f : F) (n : ℤ) : ⇑(f ^ n) = ⇑f ^ n := map_zpow coeMonoidHom f n

end DFunLike

open DFunLike

@[to_additive]
theorem mul_map_eq_one [∀ a, MulOneClass (β a)] [MulOneClass F] [MonoidFunLike F]
    {f g : F} (a : α) (h : f * g = 1) : f a * g a = 1 :=
  congrFun (coe_mul_eq_one h) a

@[to_additive]
theorem div_map' [∀ a, DivInvMonoid (β a)] [DivInvMonoid F] [MulFunLike F]
    (f g : F) (a : α) (ha : ∀ (f : F), f⁻¹ a = (f a)⁻¹) : (f / g) a = f a / g a := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_map, ha]

/-- Function application preserves inverses. -/
@[to_additive (attr := simp low) "Function application preserves negation."]
theorem inv_map [∀ a, DivisionMonoid (β a)] [Group F] [MonoidFunLike F]
    (f : F) (a : α) : f⁻¹ a = (f a)⁻¹ :=
  congrFun (coe_inv f) a

/-- Function application preserves division. -/
@[to_additive (attr := simp low) "Function application preserves subtraction."]
theorem div_map [∀ a, DivisionMonoid (β a)] [Group F] [MonoidFunLike F]
    (f g : F) (a : α) : (f / g) a = f a / g a :=
  congrFun (coe_div f g) a

@[to_additive (attr := simp low) (reorder := 8 9)]
theorem pow_map [∀ a, Monoid (β a)] [Monoid F] [MonoidFunLike F] (f : F) (n : ℕ) (a : α) :
    (f ^ n) a = f a ^ n :=
  congrFun (coe_pow f n) a

@[to_additive]
theorem zpow_map' [∀ a, DivInvMonoid (β a)] [DivInvMonoid F] [MonoidFunLike F]
    (f : F) (a : α) (ha : ∀ (f : F), f⁻¹ a = (f a)⁻¹) (n : ℤ) : (f ^ n) a = f a ^ n :=
  match n with
  | (n : ℕ) => by rw [zpow_natCast, pow_map, zpow_natCast]
  | Int.negSucc n => by rw [zpow_negSucc, ha, pow_map, ← zpow_negSucc]

/-- Function application preserves integer powers. -/
@[to_additive (attr := simp low) (reorder := 8 9) "Function application preserves integer scaling."]
theorem zpow_map [∀ a, DivisionMonoid (β a)] [Group F] [MonoidFunLike F]
    (f : F) (n : ℤ) (a : α) : (f ^ n) a = f a ^ n :=
  congrFun (coe_zpow f n) a

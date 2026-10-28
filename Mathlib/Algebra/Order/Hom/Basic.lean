/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Order.Lattice

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Basic typeclasses
* `NonnegHomClass`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `SubadditiveHomClass`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `SubmultiplicativeHomClass`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `MulLEAddHomClass`: `∀ f a b, f (a * b) ≤ f a + f b`
* `NonarchimedeanHomClass`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`Analysis.Normed.Group.Seminorm` and `Analysis.Normed.Ring.Seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

public section

assert_not_exists Ring

library_note «out-param inheritance» /--
Diamond inheritance cannot depend on `outParam`s in the following circumstances:
* there are three classes `Top`, `Middle`, `Bottom`
* all of these classes have a parameter `(α : outParam _)`
* all of these classes have an instance parameter `[Root α]` that depends on this `outParam`
* the `Root` class has two child classes: `Left` and `Right`, these are siblings in the hierarchy
* the instance `Bottom.toMiddle` takes a `[Left α]` parameter
* the instance `Middle.toTop` takes a `[Right α]` parameter
* there is a `Leaf` class that inherits from both `Left` and `Right`.

In that case, given instances `Bottom α` and `Leaf α`, Lean cannot synthesize a `Top α` instance,
even though the hypotheses of the instances `Bottom.toMiddle` and `Middle.toTop` are satisfied.

There are two workarounds:
* You could replace the bundled inheritance implemented by the instance `Middle.toTop` with
  unbundled inheritance implemented by adding a `[Top α]` parameter to the `Middle` class. This is
  the preferred option since it is also more compatible with Lean 4, at the cost of being more work
  to implement and more verbose to use.
* You could weaken the `Bottom.toMiddle` instance by making it depend on a subclass of
  `Middle.toTop`'s parameter, in this example replacing `[Left α]` with `[Leaf α]`.
-/

variable {F α β : Type*}

/-! ### Basics -/

/-- `NonnegHomClass F α β` states that `F` is a type of nonnegative morphisms. -/
class NonnegHomClass (F : Type*) (α β : outParam Type*) [Zero β] [LE β] [FunLike F α β] : Prop where
  /-- the image of any element is nonnegative. -/
  apply_nonneg (f : F) : ∀ a, 0 ≤ f a

/-- `SubadditiveHomClass F α β` states that `F` is a type of subadditive morphisms. -/
class SubadditiveHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [Add β] [LE β] [FunLike F α β] : Prop where
  /-- the image of a sum is less or equal than the sum of the images. -/
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b

/-- `SubmultiplicativeHomClass F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive SubadditiveHomClass]
class SubmultiplicativeHomClass (F : Type*) (α β : outParam (Type*)) [Mul α] [Mul β] [LE β]
    [FunLike F α β] : Prop where
  /-- the image of a product is less or equal than the product of the images. -/
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b

/-- `MulLEAddHomClass F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive SubadditiveHomClass]
class MulLEAddHomClass (F : Type*) (α β : outParam Type*) [Mul α] [Add β] [LE β] [FunLike F α β] :
    Prop where
  /-- the image of a product is less or equal than the sum of the images. -/
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b

/-- `NonarchimedeanHomClass F α β` states that `F` is a type of non-archimedean morphisms. -/
class NonarchimedeanHomClass (F : Type*) (α β : outParam Type*)
    [Add α] [LinearOrder β] [FunLike F α β] : Prop where
  /-- the image of a sum is less or equal than the maximum of the images. -/
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)

export NonnegHomClass (apply_nonneg)

export SubadditiveHomClass (map_add_le_add)

export SubmultiplicativeHomClass (map_mul_le_mul)

export MulLEAddHomClass (map_mul_le_add)

export NonarchimedeanHomClass (map_add_le_max)

attribute [simp] apply_nonneg

variable [FunLike F α β]

/-- The value at zero of a zero-preserving nonnegative homomorphism is a minimum. -/
theorem map_zero_le [Zero α] [Zero β] [LE β] [ZeroHomClass F α β] [NonnegHomClass F α β] (f : F)
    (a : α) : f 0 ≤ f a := by
  rw [map_zero]
  exact apply_nonneg f a

@[to_additive]
theorem le_map_mul_map_div [Group α] [CommMagma β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel] using map_mul_le_mul f (a / b) b

@[to_additive existing]
theorem le_map_add_map_div [Group α] [AddCommMagma β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel] using map_mul_le_add f (a / b) b

@[to_additive]
theorem le_map_div_mul_map_div [Group α] [Mul β] [LE β] [SubmultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel] using map_mul_le_mul f (a / b) (b / c)

@[to_additive existing]
theorem le_map_div_add_map_div [Group α] [Add β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
    simpa only [div_mul_div_cancel] using map_mul_le_add f (a / b) (b / c)

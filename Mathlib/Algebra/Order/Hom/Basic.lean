/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.GroupWithZero.Hom
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Ring.Defs

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

Group norms
* `AddGroupSeminormClass`: Homs are nonnegative, subadditive, even and preserve zero.
* `GroupSeminormClass`: Homs are nonnegative, respect `f (a * b) ≤ f a + f b`, `f a⁻¹ = f a` and
  preserve zero.
* `AddGroupNormClass`: Homs are seminorms such that `f x = 0 → x = 0` for all `x`.
* `GroupNormClass`: Homs are seminorms such that `f x = 0 → x = 1` for all `x`.

Ring norms
* `RingSeminormClass`: Homs are submultiplicative group norms.
* `RingNormClass`: Homs are ring seminorms that are also additive group norms.
* `MulRingSeminormClass`: Homs are ring seminorms that are multiplicative.
* `MulRingNormClass`: Homs are ring norms that are multiplicative.

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`Analysis.Normed.Group.Seminorm` and `Analysis.Normed.Ring.Seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

assert_not_exists Field

library_note "out-param inheritance"/--
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

open Function

variable {ι F α β γ δ : Type*}

/-! ### Basics -/

/-- `NonnegHomClass F α β` states that `F` is a type of nonnegative morphisms. -/
class NonnegHomClass (F : Type*) (α β : outParam Type*) [Zero β] [LE β] [FunLike F α β] : Prop where
  /-- the image of any element is non negative. -/
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

/-! ### Group (semi)norms -/


/-- `AddGroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the additive
group `α`.

You should extend this class when you extend `AddGroupSeminorm`. -/
class AddGroupSeminormClass (F : Type*) (α β : outParam Type*)
    [AddGroup α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends SubadditiveHomClass F α β where
  /-- The image of zero is zero. -/
  map_zero (f : F) : f 0 = 0
  /-- The map is invariant under negation of its argument. -/
  map_neg_eq_map (f : F) (a : α) : f (-a) = f a

/-- `GroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the group `α`.

You should extend this class when you extend `GroupSeminorm`. -/
@[to_additive]
class GroupSeminormClass (F : Type*) (α β : outParam Type*)
    [Group α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends MulLEAddHomClass F α β where
  /-- The image of one is zero. -/
  map_one_eq_zero (f : F) : f 1 = 0
  /-- The map is invariant under inversion of its argument. -/
  map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a

/-- `AddGroupNormClass F α` states that `F` is a type of `β`-valued norms on the additive group
`α`.

You should extend this class when you extend `AddGroupNorm`. -/
class AddGroupNormClass (F : Type*) (α β : outParam Type*)
    [AddGroup α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends AddGroupSeminormClass F α β where
  /-- The argument is zero if its image under the map is zero. -/
  eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0

/-- `GroupNormClass F α` states that `F` is a type of `β`-valued norms on the group `α`.

You should extend this class when you extend `GroupNorm`. -/
@[to_additive]
class GroupNormClass (F : Type*) (α β : outParam Type*)
    [Group α] [AddCommMonoid β] [PartialOrder β] [FunLike F α β] : Prop
  extends GroupSeminormClass F α β where
  /-- The argument is one if its image under the map is zero. -/
  eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1

export AddGroupSeminormClass (map_neg_eq_map)

export GroupSeminormClass (map_one_eq_zero map_inv_eq_map)

export AddGroupNormClass (eq_zero_of_map_eq_zero)

export GroupNormClass (eq_one_of_map_eq_zero)

attribute [simp] map_one_eq_zero map_neg_eq_map map_inv_eq_map

-- See note [lower instance priority]
instance (priority := 100) AddGroupSeminormClass.toZeroHomClass [AddGroup α]
    [AddCommMonoid β] [PartialOrder β] [AddGroupSeminormClass F α β] : ZeroHomClass F α β :=
  { ‹AddGroupSeminormClass F α β› with }

section GroupSeminormClass

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupSeminormClass F α β] (f : F) (x y : α)

@[to_additive]
theorem map_div_le_add : f (x / y) ≤ f x + f y := by
  rw [div_eq_mul_inv, ← map_inv_eq_map f y]
  exact map_mul_le_add _ _ _

@[to_additive]
theorem map_div_rev : f (x / y) = f (y / x) := by rw [← inv_div, map_inv_eq_map]

@[to_additive]
theorem le_map_add_map_div' : f x ≤ f y + f (y / x) := by
  simpa only [add_comm, map_div_rev, div_mul_cancel] using map_mul_le_add f (x / y) y

end GroupSeminormClass

@[to_additive]
theorem abs_sub_map_le_div [Group α] [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]
    [GroupSeminormClass F α β]
    (f : F) (x y : α) : |f x - f y| ≤ f (x / y) := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩

-- See note [lower instance priority]
@[to_additive]
instance (priority := 100) GroupSeminormClass.toNonnegHomClass [Group α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β] [GroupSeminormClass F α β] :
    NonnegHomClass F α β :=
  { ‹GroupSeminormClass F α β› with
    apply_nonneg := fun f a =>
      (nsmul_nonneg_iff two_ne_zero).1 <| by
        rw [two_nsmul, ← map_one_eq_zero f, ← div_self' a]
        exact map_div_le_add _ _ _ }

section GroupNormClass

variable [Group α] [AddCommMonoid β] [PartialOrder β] [GroupNormClass F α β] (f : F) {x : α}

@[to_additive]
theorem map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
  ⟨eq_one_of_map_eq_zero _, by
    rintro rfl
    exact map_one_eq_zero _⟩

@[to_additive]
theorem map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 :=
  (map_eq_zero_iff_eq_one _).not

end GroupNormClass

@[to_additive]
theorem map_pos_of_ne_one [Group α] [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    [GroupNormClass F α β] (f : F)
    {x : α} (hx : x ≠ 1) : 0 < f x :=
  (apply_nonneg _ _).lt_of_ne <| ((map_ne_zero_iff_ne_one _).2 hx).symm

/-! ### Ring (semi)norms -/


/-- `RingSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the ring `α`.

You should extend this class when you extend `RingSeminorm`. -/
class RingSeminormClass (F : Type*) (α β : outParam Type*)
    [NonUnitalNonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends AddGroupSeminormClass F α β, SubmultiplicativeHomClass F α β

/-- `RingNormClass F α` states that `F` is a type of `β`-valued norms on the ring `α`.

You should extend this class when you extend `RingNorm`. -/
class RingNormClass (F : Type*) (α β : outParam Type*)
    [NonUnitalNonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends RingSeminormClass F α β, AddGroupNormClass F α β

/-- `MulRingSeminormClass F α` states that `F` is a type of `β`-valued multiplicative seminorms
on the ring `α`.

You should extend this class when you extend `MulRingSeminorm`. -/
class MulRingSeminormClass (F : Type*) (α β : outParam Type*)
    [NonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends AddGroupSeminormClass F α β, MonoidWithZeroHomClass F α β

-- Lower the priority of these instances since they require synthesizing an order structure.
attribute [instance 50]
  MulRingSeminormClass.toMonoidHomClass MulRingSeminormClass.toMonoidWithZeroHomClass

/-- `MulRingNormClass F α` states that `F` is a type of `β`-valued multiplicative norms on the
ring `α`.

You should extend this class when you extend `MulRingNorm`. -/
class MulRingNormClass (F : Type*) (α β : outParam Type*)
    [NonAssocRing α] [Semiring β] [PartialOrder β] [FunLike F α β] : Prop
  extends MulRingSeminormClass F α β, AddGroupNormClass F α β

-- See note [out-param inheritance]
-- See note [lower instance priority]
instance (priority := 100) RingSeminormClass.toNonnegHomClass [NonUnitalNonAssocRing α]
    [Semiring β] [LinearOrder β] [IsOrderedAddMonoid β] [RingSeminormClass F α β] :
    NonnegHomClass F α β :=
  AddGroupSeminormClass.toNonnegHomClass

-- See note [lower instance priority]
instance (priority := 100) MulRingSeminormClass.toRingSeminormClass [NonAssocRing α]
    [Semiring β] [PartialOrder β] [MulRingSeminormClass F α β] : RingSeminormClass F α β :=
  { ‹MulRingSeminormClass F α β› with map_mul_le_mul := fun _ _ _ => (map_mul _ _ _).le }

-- See note [lower instance priority]
instance (priority := 100) MulRingNormClass.toRingNormClass [NonAssocRing α]
    [Semiring β] [PartialOrder β] [MulRingNormClass F α β] : RingNormClass F α β :=
  { ‹MulRingNormClass F α β›, MulRingSeminormClass.toRingSeminormClass with }

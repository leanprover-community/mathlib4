/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Hom.Basic

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Group norms
* `AddGroupSeminormClass`: Homs are nonnegative, subadditive, even and preserve zero.
* `GroupSeminormClass`: Homs are nonnegative, respect `f (a * b) ≤ f a + f b`, `f a⁻¹ = f a` and
  preserve zero.
* `AddGroupNormClass`: Homs are seminorms such that `f x = 0 → x = 0` for all `x`.
* `GroupNormClass`: Homs are seminorms such that `f x = 0 → x = 1` for all `x`.

## Notes

Typeclasses for seminorms are defined here while types of seminorms are defined in
`Analysis.Normed.Group.Seminorm` and `Analysis.Normed.Ring.Seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

public section

assert_not_exists Ring

variable {F α β : Type*} [FunLike F α β]

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
theorem map_inv_mul {α : Type*} [FunLike F α β] [CommGroup α] [GroupSeminormClass F α β] (x y : α) :
    f (x⁻¹ * y) = f (x * y⁻¹) := by
  rw [← map_inv_eq_map, inv_mul', inv_inv, div_eq_mul_inv]

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
      (nsmul_nonneg_iff (Nat.succ_ne_zero 1)).1 <| by
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

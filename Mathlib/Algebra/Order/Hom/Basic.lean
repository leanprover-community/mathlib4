/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module algebra.order.hom.basic
! leanprover-community/mathlib commit 70d50ecfd4900dd6d328da39ab7ebd516abe4025
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Algebra.GroupPower.Order
import Mathlib.Tactic.Positivity

/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

Basic typeclasses
* `NonNegHomClass`: Homs are nonnegative: `∀ f a, 0 ≤ f a`
* `SubAdditiveHomClass`: Homs are subadditive: `∀ f a b, f (a + b) ≤ f a + f b`
* `SubMultiplicativeHomClass`: Homs are submultiplicative: `∀ f a b, f (a * b) ≤ f a * f b`
* `MulLEAddHomClass`: `∀ f a b, f (a * b) ≤ f a + f b`
* `NonArchimedeanHomClass`: `∀ a b, f (a + b) ≤ max (f a) (f b)`

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
`analysis.normed.group.seminorm` and `analysis.normed.ring.seminorm` because absolute values are
multiplicative ring norms but outside of this use we only consider real-valued seminorms.

## TODO

Finitary versions of the current lemmas.
-/

set_option autoImplicit false

open Function

variable {ι F α β γ δ : Type _}

/-- `NonNegHomClass F α β` states that `F` is a type of nonnegative morphisms. -/
class NonNegHomClass (F : Type _) (α β : outParam (Type _)) [Zero β] [LE β] extends
  FunLike F α fun _ => β where
  /-- the image of any element is non negative. -/
  map_nonneg (f : F) : ∀ a, 0 ≤ f a
#align NonNegHomClass NonNegHomClass

/-- `SubAdditiveHomClass F α β` states that `F` is a type of subadditive morphisms. -/
class SubAdditiveHomClass (F : Type _) (α β : outParam (Type _)) [Add α] [Add β] [LE β] extends
  FunLike F α fun _ => β where
  /-- the image of a sum is less or equal than the sum of the images. -/
  map_add_le_add (f : F) : ∀ a b, f (a + b) ≤ f a + f b
#align subadditive_hom_class SubAdditiveHomClass

/-- `SubMultiplicativeHomClass F α β` states that `F` is a type of submultiplicative morphisms. -/
@[to_additive SubAdditiveHomClass]
class SubMultiplicativeHomClass (F : Type _) (α β : outParam (Type _)) [Mul α] [Mul β] [LE β]
  extends FunLike F α fun _ => β where
  /-- the image of a product is less or equal than the product of the images. -/
  map_mul_le_mul (f : F) : ∀ a b, f (a * b) ≤ f a * f b
#align SubMultiplicativeHomClass SubMultiplicativeHomClass

/-- `MulLEAddHomClass F α β` states that `F` is a type of subadditive morphisms. -/
@[to_additive SubAdditiveHomClass]
class MulLEAddHomClass (F : Type _) (α β : outParam (Type _)) [Mul α] [Add β] [LE β]
  extends FunLike F α fun _ => β where
  /-- the image of a product is less or equal than the sum of the images. -/
  map_mul_le_add (f : F) : ∀ a b, f (a * b) ≤ f a + f b
#align mul_le_add_hom_class MulLEAddHomClass

/-- `NonArchimedeanHomClass F α β` states that `F` is a type of non-archimedean morphisms. -/
class NonArchimedeanHomClass (F : Type _) (α β : outParam (Type _)) [Add α] [LinearOrder β]
  extends FunLike F α fun _ => β where
  /-- the image of a sum is less or equal than the maximum of the images. -/
  map_add_le_max (f : F) : ∀ a b, f (a + b) ≤ max (f a) (f b)
#align nonarchimedean_hom_class NonArchimedeanHomClass

export NonNegHomClass (map_nonneg)

export SubAdditiveHomClass (map_add_le_add)

export SubMultiplicativeHomClass (map_mul_le_mul)

export MulLEAddHomClass (map_mul_le_add)

export NonArchimedeanHomClass (map_add_le_max)

attribute [simp] map_nonneg

@[to_additive]
theorem le_map_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubMultiplicativeHomClass F α β]
    (f : F) (a b : α) : f a ≤ f b * f (a / b) := by
  simpa only [mul_comm, div_mul_cancel'] using map_mul_le_mul f (a / b) b
#align le_map_mul_map_div le_map_mul_map_div

@[to_additive]
theorem le_map_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β] (f : F)
    (a b : α) : f a ≤ f b + f (a / b) := by
  simpa only [add_comm, div_mul_cancel'] using map_mul_le_add f (a / b) b
#align le_map_add_map_div le_map_add_map_div

@[to_additive]
theorem le_map_div_mul_map_div [Group α] [CommSemigroup β] [LE β] [SubMultiplicativeHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) * f (b / c) := by
  simpa only [div_mul_div_cancel'] using map_mul_le_mul f (a / b) (b / c)
#align le_map_div_mul_map_div le_map_div_mul_map_div

@[to_additive]
theorem le_map_div_add_map_div [Group α] [AddCommSemigroup β] [LE β] [MulLEAddHomClass F α β]
    (f : F) (a b c : α) : f (a / c) ≤ f (a / b) + f (b / c) := by
    simpa only [div_mul_div_cancel'] using map_mul_le_add f (a / b) (b / c)
#align le_map_div_add_map_div le_map_div_add_map_div

--namespace Mathlib.Meta.Positivity

--Porting note: tactic extension commented as decided in the weekly porting meeting
-- /-- Extension for the `positivity` tactic: nonnegative maps take nonnegative values. -/
-- @[positivity _ _]
-- unsafe def positivity_map : expr → tactic strictness
--   | expr.app (quote.1 ⇑(%%f)) (quote.1 (%%ₓa)) => nonnegative <$> mk_app `` map_nonneg [f, a]
--   | _ => failed
-- #align tactic.positivity_map tactic.positivity_map

--end Mathlib.Meta.Positivity

/-! ### Group (semi)norms -/

/-- `AddGroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the additive
group `α`.

You should extend this class when you extend `AddGroupSeminorm`. -/
class AddGroupSeminormClass (F : Type _) (α β : outParam $ Type _) [AddGroup α]
  [OrderedAddCommMonoid β] extends SubAdditiveHomClass F α β :=
(map_zero (f : F) : f 0 = 0)
(map_neg_eq_map (f : F) (a : α) : f (-a) = f a)

/-- `GroupSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the group `α`.

You should extend this class when you extend `GroupSeminorm`. -/
@[to_additive]
class GroupSeminormClass (F : Type _) (α β : outParam $ Type _) [Group α] [OrderedAddCommMonoid β]
  extends MulLEAddHomClass F α β :=
(map_one_eq_zero (f : F) : f 1 = 0)
(map_inv_eq_map (f : F) (a : α) : f a⁻¹ = f a)

/-- `AddGroupNormClass F α` states that `F` is a type of `β`-valued norms on the additive group
`α`.

You should extend this class when you extend `AddGroupNorm`. -/
class AddGroupNormClass (F : Type _) (α β : outParam $ Type _) [AddGroup α] [OrderedAddCommMonoid β]
  extends AddGroupSeminormClass F α β :=
(eq_zero_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 0)

/-- `GroupNormClass F α` states that `F` is a type of `β`-valued norms on the group `α`.

You should extend this class when you extend `GroupNorm`. -/
@[to_additive]
class GroupNormClass (F : Type _) (α β : outParam $ Type _) [Group α] [OrderedAddCommMonoid β]
  extends GroupSeminormClass F α β :=
(eq_one_of_map_eq_zero (f : F) {a : α} : f a = 0 → a = 1)

export AddGroupSeminormClass    (map_neg_eq_map)
export GroupSeminormClass        (map_one_eq_zero map_inv_eq_map)
export AddGroupNormClass        (eq_zero_of_map_eq_zero)
export GroupNormClass            (eq_one_of_map_eq_zero)

attribute [simp] map_one_eq_zero
attribute [simp] map_neg_eq_map
attribute [simp] map_inv_eq_map

-- See note [lower instance priority]
instance (priority := 100) AddGroupSeminormClass.to_ZeroHomClass [AddGroup α]
  [OrderedAddCommMonoid β] [AddGroupSeminormClass F α β] : ZeroHomClass F α β :=
{ ‹AddGroupSeminormClass F α β› with }

section GroupSeminormClass
variable [Group α] [OrderedAddCommMonoid β] [GroupSeminormClass F α β] (f : F) (x y : α)

@[to_additive] lemma map_div_le_add : f (x / y) ≤ f x + f y :=
by rw [div_eq_mul_inv, ←map_inv_eq_map f y]; exact map_mul_le_add _ _ _

@[to_additive] lemma map_div_rev : f (x / y) = f (y / x) := by rw [←inv_div, map_inv_eq_map]

@[to_additive] lemma le_map_add_map_div' : f x ≤ f y + f (y / x) :=
by simpa only [add_comm, map_div_rev, div_mul_cancel'] using map_mul_le_add f (x / y) y

end GroupSeminormClass

example [OrderedAddCommGroup β] : OrderedAddCommMonoid β := inferInstance

@[to_additive] lemma abs_sub_map_le_div [Group α] [LinearOrderedAddCommGroup β]
  [GroupSeminormClass F α β] (f : F) (x y : α) : |f x - f y| ≤ f (x / y) := by
  rw [abs_sub_le_iff, sub_le_iff_le_add', sub_le_iff_le_add']
  exact ⟨le_map_add_map_div _ _ _, le_map_add_map_div' _ _ _⟩

@[to_additive] -- See note [lower instance priority]
instance (priority := 100) GroupSeminormClass.to_NonNegHomClass [Group α]
  [LinearOrderedAddCommMonoid β] [GroupSeminormClass F α β] :
  NonNegHomClass F α β :=
{ ‹GroupSeminormClass F α β› with
  map_nonneg := fun f a ↦ (nsmul_nonneg_iff two_ne_zero).1 $
    by rw [two_nsmul, ←map_one_eq_zero f, ←div_self' a]; exact map_div_le_add _ _ _ }

section GroupNormClass
variable [Group α] [OrderedAddCommMonoid β] [GroupNormClass F α β] (f : F) {x : α}

@[simp, to_additive] lemma map_eq_zero_iff_eq_one : f x = 0 ↔ x = 1 :=
⟨eq_one_of_map_eq_zero _, by rintro rfl; exact map_one_eq_zero _⟩

@[to_additive] lemma map_ne_zero_iff_ne_one : f x ≠ 0 ↔ x ≠ 1 := (map_eq_zero_iff_eq_one _).not

end GroupNormClass

@[to_additive] lemma map_pos_of_ne_one [Group α] [LinearOrderedAddCommMonoid β]
  [GroupNormClass F α β] (f : F) {x : α} (hx : x ≠ 1) : 0 < f x :=
(map_nonneg _ _).lt_of_ne $ ((map_ne_zero_iff_ne_one _).2 hx).symm

/-! ### Ring (semi)norms -/

/-- `RingSeminormClass F α` states that `F` is a type of `β`-valued seminorms on the ring `α`.

You should extend this class when you extend `ring_seminorm`. -/
class RingSeminormClass (F : Type _) (α β : outParam $ Type _) [NonUnitalNonAssocRing α]
  [OrderedSemiring β] extends AddGroupSeminormClass F α β, SubMultiplicativeHomClass F α β

/-- `RingNormClass F α` states that `F` is a type of `β`-valued norms on the ring `α`.

You should extend this class when you extend `ring_norm`. -/
class RingNormClass (F : Type _) (α β : outParam $ Type _) [NonUnitalNonAssocRing α]
  [OrderedSemiring β] extends RingSeminormClass F α β, AddGroupNormClass F α β

/-- `MulRingSeminormClass F α` states that `F` is a type of `β`-valued multiplicative seminorms
on the ring `α`.

You should extend this class when you extend `mul_ring_seminorm`. -/
class MulRingSeminormClass (F : Type _) (α β : outParam $ Type _) [NonAssocRing α]
  [OrderedSemiring β] extends AddGroupSeminormClass F α β, MonoidWithZeroHomClass F α β

/-- `MulRingNormClass F α` states that `F` is a type of `β`-valued multiplicative norms on the
ring `α`.

You should extend this class when you extend `mul_ring_norm`. -/
class MulRingNormClass (F : Type _) (α β : outParam $ Type _) [NonAssocRing α]
  [OrderedSemiring β] extends MulRingSeminormClass F α β, AddGroupNormClass F α β

-- TODO: Somehow this does not get inferred.
-- See note [lower instance priority]
instance (priority := 100) RingSeminormClass.to_NonNegHomClass [NonUnitalNonAssocRing α]
  [LinearOrderedSemiring β] [RingSeminormClass F α β] : NonNegHomClass F α β :=
AddGroupSeminormClass.to_NonNegHomClass

-- See note [lower instance priority]
instance (priority := 100) MulRingSeminormClass.to_RingSeminormClass [NonAssocRing α]
  [OrderedSemiring β] [MulRingSeminormClass F α β] : RingSeminormClass F α β :=
{ ‹MulRingSeminormClass F α β› with
  map_mul_le_mul := fun f a b ↦ (map_mul _ _ _).le }

-- See note [lower instance priority]
instance (priority := 100) MulRingNormClass.to_RingNormClass [NonAssocRing α] [OrderedSemiring β]
  [MulRingNormClass F α β] : RingNormClass F α β :=
{ ‹MulRingNormClass F α β›, MulRingSeminormClass.to_RingSeminormClass with }

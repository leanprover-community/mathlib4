/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.GroupWithZero.Hom
public import Mathlib.Algebra.Order.Hom.GroupNormClass
public import Mathlib.Algebra.Ring.Defs


/-!
# Algebraic order homomorphism classes

This file defines hom classes for common properties at the intersection of order theory and algebra.

## Typeclasses

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

public section

assert_not_exists Field

variable {F α β : Type*}

variable [FunLike F α β]

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

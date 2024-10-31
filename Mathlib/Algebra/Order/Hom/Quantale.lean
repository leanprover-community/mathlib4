/-
Copyright (c) 2024 Pieter Cuijpers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pieter Cuijpers
-/
import Mathlib.Algebra.Group.Hom.Defs
import Mathlib.Algebra.Order.Hom.Basic
import Mathlib.Algebra.Order.Hom.Monoid
import Mathlib.Algebra.Order.Quantale
import Mathlib.Data.FunLike.Basic
import Mathlib.Order.Hom.CompleteLattice

/-!
# Algebraic order homomorphism classes

This file defines hom classes for quantales, derived from those for the intersection between
algebra and order theory in Mathlib.Algebra.Order.Hom.Basic.

## Typeclasses

Basic typeclasses for quantales
* `QuantaleHom` : Homs are Semigroup Homs as well as CompleteLattice Homs
* `LaxQuantaleHom` : Homs are Submultiplicative Semigroup Homs as well as CompleteLattice Homs
* `OplaxQuantaleHom` : Homs are Supermultiplicative Semigroup Homs as well as CompleteLattice Homs
* And their additive versions

Basic typeclasses for unital quantales, i.e. quantales over a monoid
* `OneQuantaleHom` : Homs are Monoid Homs as well as CompleteLattice Homs
* `LaxOneQuantaleHom` : Homs are Submultiplicative Monoid Homs as well as CompleteLattice Homs
* `OplaxOneQuantaleHom` : Homs are Supermultiplicative Monoid Homs as well as CompleteLattice Homs
* And their additive versions

-/

open Function

namespace AddQuantale

variable {F : Type*} {α β : outParam Type*}
variable [AddSemigroup α] [AddSemigroup β] [AddQuantale α] [AddQuantale β] [FunLike F α β]

/-- `AddQuantaleHomClass F α β` states that `F` is a type of additive quantale morphisms. -/
class AddQuantaleHomClass extends AddHomClass F α β, CompleteLatticeHomClass F α β : Prop

/-- `AddQuantaleHom α β` is a type of additive quantale morphisms. -/
structure AddQuantaleHom extends AddHom α β, CompleteLatticeHom α β

/-- `ZeroAddQuantaleHomClass F α β` states that `F` is a type of unital additive quantale
morphisms. -/
class ZeroAddQuantaleHomClass [AddMonoid α] [AddMonoid β]
  extends AddMonoidHomClass F α β, CompleteLatticeHomClass F α β : Prop

/-- `ZeroAddQuantaleHom α β` is a type of unital additive quantale morphisms. -/
structure ZeroAddQuantaleHom [AddMonoid α] [AddMonoid β]
  extends AddMonoidHom α β, CompleteLatticeHom α β

/-- `LaxAddQuantaleHomClass F α β` states that `F` is a type of unital additive quantale
morphisms. -/
class LaxAddQuantaleHomClass [AddMonoid α] [AddMonoid β]
  extends SubadditiveHomClass F α β, NonnegHomClass F α β, CompleteLatticeHomClass F α β : Prop

-- In `Mathlib.Algebra.Order.Hom.Basic` there are only definitions for HomClasses and not
-- for the associated Homs themselves. Those we need to introduce explicitly here, apparently.
-- I need to check why this is the case (I have a hunch that they are not considered in isolation
-- usually, so standalone Hom definitions are futile.)

variable {F : Type*} {α β : outParam Type*}
variable [AddSemigroup α] [AddSemigroup β] [AddQuantale α] [AddQuantale β] [FunLike F α β]

end AddQuantale

namespace Quantale

variable {F : Type*} {α β : outParam Type*}
variable [Semigroup α] [Semigroup β] [Quantale α] [Quantale β] [FunLike F α β]

/-- `QuantaleHomClass F α β` states that `F` is a type of additive quantale morphisms. -/
@[to_additive]
class QuantaleHomClass extends MulHomClass F α β, CompleteLatticeHomClass F α β : Prop

/-- `QuantaleHom α β` is a type of additive quantale morphisms. -/
@[to_additive]
structure QuantaleHom extends MulHom α β, CompleteLatticeHom α β

/-- `OneQuantaleHomClass F α β` states that `F` is a type of unital additive quantale
morphisms. -/
@[to_additive]
class OneQuantaleHomClass [Monoid α] [Monoid β]
  extends MonoidHomClass F α β, CompleteLatticeHomClass F α β : Prop

/-- `OneQuantaleHom α β` is a type of unital additive quantale morphisms. -/
@[to_additive]
structure OneQuantaleHom [Monoid α] [Monoid β]
  extends MonoidHom α β, CompleteLatticeHom α β

end Quantale

/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Order.Filter.Germ.Basic

/-!
# Ordered monoid instances on the space of germs of a function at a filter

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* `OrderedCancelCommMonoid` and `OrderedCancelAddCommMonoid`.

## Tags

filter, germ
-/

namespace Filter.Germ

variable {α : Type*} {β : Type*} {l : Filter α}

@[to_additive]
instance instIsOrderedMonoid [CommMonoid β] [PartialOrder β] [IsOrderedMonoid β] :
    IsOrderedMonoid (Germ l β) where
  mul_le_mul_left f g := inductionOn₂ f g fun _ _ H h ↦ inductionOn h fun _ ↦ H.mono
    fun _ H ↦ mul_le_mul_left' H _

@[to_additive]
instance instIsOrderedCancelMonoid [CommMonoid β] [PartialOrder β] [IsOrderedCancelMonoid β] :
    IsOrderedCancelMonoid (Germ l β) where
  le_of_mul_le_mul_left f g h := inductionOn₃ f g h fun _ _ _ H ↦ H.mono
    fun _ ↦ le_of_mul_le_mul_left'

@[to_additive]
instance instCanonicallyOrderedMul [Mul β] [LE β] [CanonicallyOrderedMul β] :
    CanonicallyOrderedMul (Germ l β) where
  le_mul_self x y := inductionOn₂ x y fun _ _ ↦ Eventually.of_forall fun _ ↦ le_mul_self
  le_self_mul x y := inductionOn₂ x y fun _ _ ↦ Eventually.of_forall fun _ ↦ le_self_mul

end Filter.Germ

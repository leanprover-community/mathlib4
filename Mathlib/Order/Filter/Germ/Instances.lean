/-
Copyright (c) 2020 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Abhimanyu Pallavi Sudhir
-/
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Order.Filter.Germ.Basic

#align_import order.filter.germ from "leanprover-community/mathlib"@"1f0096e6caa61e9c849ec2adbd227e960e9dff58"

/-!
# Ordered monoid instances on germ of a function at a filter

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* `OrderedCancelCommMonoid` and `OrderedCancelAddCommMonoid`.

## Tags

filter, germ
-/

namespace Filter.Germ

variable {α : Type*} {β : Type*} {l : Filter α}

@[to_additive]
instance instOrderedCommMonoid [OrderedCommMonoid β] : OrderedCommMonoid (Germ l β) where
  mul_le_mul_left f g := inductionOn₂ f g fun _f _g H h ↦ inductionOn h fun _h ↦ H.mono
    fun _x H ↦ mul_le_mul_left' H _

@[to_additive]
instance instOrderedCancelCommMonoid [OrderedCancelCommMonoid β] :
    OrderedCancelCommMonoid (Germ l β) where
  le_of_mul_le_mul_left f g h := inductionOn₃ f g h fun _f _g _h H ↦ H.mono
    fun _x ↦ le_of_mul_le_mul_left'

@[to_additive]
instance instCanonicallyOrderedCommMonoid [CanonicallyOrderedCommMonoid β] :
    CanonicallyOrderedCommMonoid (Germ l β) where
  __ := instExistsMulOfLE
  le_self_mul x y := inductionOn₂ x y fun _ _ ↦ eventually_of_forall fun _ ↦ le_self_mul


/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathbin.Algebra.Group.Prod
import Mathbin.Algebra.Order.Monoid.Cancel.Defs
import Mathbin.Algebra.Order.Monoid.Canonical.Defs

/-! # Products of ordered monoids -/


namespace Prod

variable {α β M N : Type _}

@[to_additive]
instance [OrderedCommMonoid α] [OrderedCommMonoid β] : OrderedCommMonoid (α × β) :=
  { Prod.commMonoid, Prod.partialOrder _ _ with
    mul_le_mul_left := fun a b h c => ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩ }

@[to_additive]
instance [OrderedCancelCommMonoid M] [OrderedCancelCommMonoid N] :
    OrderedCancelCommMonoid (M × N) :=
  { Prod.orderedCommMonoid with
    le_of_mul_le_mul_left := fun a b c h =>
      ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
instance [LE α] [LE β] [Mul α] [Mul β] [HasExistsMulOfLe α] [HasExistsMulOfLe β] :
    HasExistsMulOfLe (α × β) :=
  ⟨fun a b h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), ext hc hd⟩⟩

@[to_additive]
instance [CanonicallyOrderedMonoid α] [CanonicallyOrderedMonoid β] :
    CanonicallyOrderedMonoid (α × β) :=
  { Prod.orderedCommMonoid, Prod.orderBot _ _, Prod.has_exists_mul_of_le with
    le_self_mul := fun a b => ⟨le_self_mul, le_self_mul⟩ }

end Prod


/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Monoid.Cancel.Defs
import Mathlib.Algebra.Order.Monoid.Canonical.Defs

#align_import algebra.order.monoid.prod from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Products of ordered monoids -/

namespace Prod

variable {α β M N : Type _}

@[to_additive]
instance [OrderedCommMonoid α] [OrderedCommMonoid β] : OrderedCommMonoid (α × β) :=
  { mul_le_mul_left := fun _ _ h _ ↦ ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩ }

@[to_additive]
instance [OrderedCancelCommMonoid M] [OrderedCancelCommMonoid N] :
    OrderedCancelCommMonoid (M × N) :=
  { (inferInstance : OrderedCommMonoid (M × N)) with
    le_of_mul_le_mul_left :=
      fun _ _ _ h ↦ ⟨le_of_mul_le_mul_left' h.1, le_of_mul_le_mul_left' h.2⟩ }

@[to_additive]
instance [LE α] [LE β] [Mul α] [Mul β] [ExistsMulOfLE α] [ExistsMulOfLE β] :
    ExistsMulOfLE (α × β) :=
  ⟨fun h =>
    let ⟨c, hc⟩ := exists_mul_of_le h.1
    let ⟨d, hd⟩ := exists_mul_of_le h.2
    ⟨(c, d), ext hc hd⟩⟩

@[to_additive]
instance [Mul α] [LE α] [CanonicallyOrderedMul α]
    [Mul β] [LE β] [CanonicallyOrderedMul β] :
    CanonicallyOrderedMul (α × β) :=
  { (inferInstance : ExistsMulOfLE _) with
      le_self_mul := fun _ _ ↦ ⟨le_self_mul, le_self_mul⟩
      le_mul_self := fun _ _ ↦ ⟨le_mul_self, le_mul_self⟩ }

end Prod

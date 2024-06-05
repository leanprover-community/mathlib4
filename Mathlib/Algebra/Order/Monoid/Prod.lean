/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Group.Prod
import Mathlib.Algebra.Order.Group.Synonym
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Prod.Lex

#align_import algebra.order.monoid.prod from "leanprover-community/mathlib"@"2258b40dacd2942571c8ce136215350c702dc78f"

/-! # Products of ordered monoids -/

assert_not_exists MonoidWithZero

namespace Prod

variable {α β : Type*}

@[to_additive]
instance [OrderedCommMonoid α] [OrderedCommMonoid β] : OrderedCommMonoid (α × β) where
  mul_le_mul_left _ _ h _ := ⟨mul_le_mul_left' h.1 _, mul_le_mul_left' h.2 _⟩

@[to_additive]
instance instOrderedCancelCommMonoid [OrderedCancelCommMonoid α] [OrderedCancelCommMonoid β] :
    OrderedCancelCommMonoid (α × β) :=
  { (inferInstance : OrderedCommMonoid (α × β)) with
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
instance [CanonicallyOrderedCommMonoid α] [CanonicallyOrderedCommMonoid β] :
    CanonicallyOrderedCommMonoid (α × β) :=
  { (inferInstance : OrderedCommMonoid _), (inferInstance : OrderBot _),
    (inferInstance : ExistsMulOfLE _) with
      le_self_mul := fun _ _ ↦ ⟨le_self_mul, le_self_mul⟩ }

namespace Lex

@[to_additive]
instance orderedCommMonoid [OrderedCommMonoid α]
    [CovariantClass α α (· * ·) (· < ·)] [OrderedCommMonoid β] :
    OrderedCommMonoid (α ×ₗ β) where
  mul_le_mul_left _ _ hxy z := ((le_iff _ _).1 hxy).elim
    (fun hxy => left _ _ <| mul_lt_mul_left' hxy _)
    -- Note: the `congr_arg` used to be `rw [hxy.1]` before #8386
    -- but the definition of `Mul.mul` got unfolded differently.
    (fun hxy => (le_iff _ _).2 <| Or.inr ⟨congr_arg (z.1 * ·) hxy.1, mul_le_mul_left' hxy.2 _⟩)

@[to_additive]
instance orderedCancelCommMonoid [OrderedCancelCommMonoid α] [OrderedCancelCommMonoid β] :
    OrderedCancelCommMonoid (α ×ₗ β) where
  mul_le_mul_left _ _ := mul_le_mul_left'
  le_of_mul_le_mul_left _ _ _ hxyz := ((le_iff _ _).1 hxyz).elim
    (fun hxy => left _ _ <| lt_of_mul_lt_mul_left' hxy)
    (fun hxy => (le_iff _ _).2 <| Or.inr ⟨mul_left_cancel hxy.1, le_of_mul_le_mul_left' hxy.2⟩)

@[to_additive]
instance linearOrderedCancelCommMonoid [LinearOrderedCancelCommMonoid α]
    [LinearOrderedCancelCommMonoid β] : LinearOrderedCancelCommMonoid (α ×ₗ β) where
  __ : LinearOrder (α ×ₗ β) := inferInstance
  __ : OrderedCancelCommMonoid (α ×ₗ β) := inferInstance

end Lex

end Prod

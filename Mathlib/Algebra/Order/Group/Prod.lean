/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Products of ordered commutative groups.
-/


namespace Prod

variable {G H : Type*}

@[to_additive]
instance [OrderedCommGroup G] [OrderedCommGroup H] : OrderedCommGroup (G × H) :=
  { Prod.instCommGroup, Prod.instPartialOrder G H, Prod.instOrderedCancelCommMonoid
    with }

namespace Lex

@[to_additive]
instance orderedCommGroup [OrderedCommGroup G] [OrderedCommGroup H] :
    OrderedCommGroup (G ×ₗ H) where
  mul_le_mul_left _ _ := mul_le_mul_left'

@[to_additive]
instance linearOrderedCommGroup [LinearOrderedCommGroup G] [LinearOrderedCommGroup H] :
    LinearOrderedCommGroup (G ×ₗ H) where
  __ : LinearOrder (G ×ₗ H) := inferInstance
  mul_le_mul_left _ _ := mul_le_mul_left'

end Lex

end Prod

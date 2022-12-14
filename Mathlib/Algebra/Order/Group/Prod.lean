/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Products of ordered commutative groups.
-/


variable {α : Type _}

namespace Prod

variable {G H : Type _}

@[to_additive]
instance [OrderedCommGroup G] [OrderedCommGroup H] : OrderedCommGroup (G × H) :=
  { Prod.commGroup, Prod.partialOrder G H, Prod.orderedCancelCommMonoid with }

end Prod

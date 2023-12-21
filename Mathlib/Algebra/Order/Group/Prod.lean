/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Algebra.Order.Group.Instances
import Mathlib.Algebra.Order.Monoid.Prod

#align_import algebra.order.group.prod from "leanprover-community/mathlib"@"ee0c179cd3c8a45aa5bffbf1b41d8dbede452865"

/-!
# Products of ordered commutative groups.
-/


variable {α : Type*}

namespace Prod

variable {G H : Type*}

@[to_additive]
instance [OrderedCommGroup G] [OrderedCommGroup H] : OrderedCommGroup (G × H) :=
  { Prod.instCommGroup, Prod.instPartialOrder G H, Prod.instOrderedCancelCommMonoid
    with }

end Prod

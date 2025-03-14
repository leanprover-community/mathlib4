/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Prod
import Mathlib.Algebra.Order.Monoid.Prod

/-!
# Products of ordered rings
-/

variable {α β : Type*}

instance [OrderedSemiring α] [OrderedSemiring β] : OrderedSemiring (α × β) :=
  { inferInstanceAs (Semiring (α × β)), inferInstanceAs (OrderedAddCommMonoid (α × β)) with
    zero_le_one := ⟨zero_le_one, zero_le_one⟩
    mul_le_mul_of_nonneg_left := fun _ _ _ hab hc =>
      ⟨mul_le_mul_of_nonneg_left hab.1 hc.1, mul_le_mul_of_nonneg_left hab.2 hc.2⟩
    mul_le_mul_of_nonneg_right := fun _ _ _ hab hc =>
      ⟨mul_le_mul_of_nonneg_right hab.1 hc.1, mul_le_mul_of_nonneg_right hab.2 hc.2⟩ }

instance [OrderedCommSemiring α] [OrderedCommSemiring β] : OrderedCommSemiring (α × β) :=
  { inferInstanceAs (OrderedSemiring (α × β)), inferInstanceAs (CommSemiring (α × β)) with }

instance [OrderedRing α] [OrderedRing β] : OrderedRing (α × β) :=
  { inferInstanceAs (Ring (α × β)), inferInstanceAs (OrderedSemiring (α × β)) with
    mul_nonneg := fun _ _ ha hb => ⟨mul_nonneg ha.1 hb.1, mul_nonneg ha.2 hb.2⟩ }

instance [OrderedCommRing α] [OrderedCommRing β] : OrderedCommRing (α × β) :=
  { inferInstanceAs (OrderedRing (α × β)), inferInstanceAs (CommRing (α × β)) with }

/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Ring.Defs

#align_import algebra.order.ring.char_zero from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

/-!
# Strict ordered semiring have characteristic zero
-/


variable {α : Type*}

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.to_charZero [StrictOrderedSemiring α] :
    CharZero α :=
  ⟨StrictMono.injective <|
      strictMono_nat_of_lt_succ fun n => by
        rw [Nat.cast_succ]
        apply lt_add_one⟩
#align strict_ordered_semiring.to_char_zero StrictOrderedSemiring.to_charZero

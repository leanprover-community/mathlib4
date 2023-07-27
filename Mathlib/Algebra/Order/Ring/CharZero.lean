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


variable {α : Type _}

/-- The type class assumptions here are the minimal ones required to ensure `CharZero R`. While
all of these are implied by `[StrictOrderedSemiring R]`, this generalization isn't superfluous;
these conditions are also satisfied by the conjunction of `[NonUnitalRing R]`, `[PartialOrder R]`,
`[StarOrderedRing R]`, `[Nontrivial R]` (and these do not imply `StrictOrderedSemiring R`). This
instance gives us access to several lemmas involving `Nat.cast`, such as `Nat.strictMono_cast` for
each of `R`, `selfAdjoint R` and `StarOrderedRing.positive R`.

Note, we assign the priority on this instance lower than `StrictOrderedSemiring.to_CharZero` so
that Lean finds that instance first for the most common use case. This doesn't lead to expensive
`isDefEq` checks because `CharZero α : Prop`. -/
-- see Note [lower instance priority]
instance (priority := 50) AddMonoidWithOne.instCharZero [AddMonoidWithOne α]
  [NeZero (1 : α)] [PartialOrder α] [CovariantClass α α (· + ·) (· < ·)] [ZeroLEOneClass α] :
    CharZero α where
  cast_injective := StrictMono.injective <| strictMono_nat_of_lt_succ fun n => by
    rw [Nat.cast_succ]
    apply lt_add_one

-- see Note [lower instance priority]
instance (priority := 100) StrictOrderedSemiring.to_charZero [StrictOrderedSemiring α] :
    CharZero α :=
  inferInstance
#align strict_ordered_semiring.to_char_zero StrictOrderedSemiring.to_charZero

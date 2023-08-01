/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro
-/
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.NatCast

#align_import algebra.order.ring.char_zero from "leanprover-community/mathlib"@"655994e298904d7e5bbd1e18c95defd7b543eb94"

/-!
# Strict ordered additive commutative monoids with one have characteristic zero

An ordered additive commutative monoid with one in which addition is strictly monotone and `0 ≠ 1`
has characteristic zero. This includes `StrictOrderedSemiring`s as well as `StarOrderedRing R` where
`R` is a `Ring`.
-/


variable {α : Type _}

-- see Note [lower instance priority]
instance (priority := 100) OrderedAddCommMonoidWithOne.to_charZero
    [OrderedAddCommMonoidWithOne α] [CovariantClass α α (· + ·) (· < · )] [NeZero (1 : α)] :
    CharZero α :=
  ⟨StrictMono.injective <|
      strictMono_nat_of_lt_succ fun n => by
        rw [Nat.cast_succ]
        apply lt_add_one⟩
-- note: the `ₓ` is because this used to be stated only for `StrictOrderedSemiring α`.
#align strict_ordered_semiring.to_char_zero OrderedAddCommMonoidWithOne.to_charZeroₓ

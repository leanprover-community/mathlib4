/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury KudryashovJ
-/
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Data.Set.Pointwise.Basic

/-!

# Pointwise multiplication of sets preserves boundedness above.

TODO: Can be combined with future results about pointwise multiplication on sets that use
ordered algebraic classes.

-/

variable {α : Type*}

namespace Set

open Pointwise

@[to_additive]
theorem BddAbove.mul [OrderedCommMonoid α] {A B : Set α} (hA : BddAbove A) (hB : BddAbove B) :
    BddAbove (A * B) :=
  hA.image2 (fun _ _ _ h ↦ mul_le_mul_right' h _) (fun _ _ _ h ↦ mul_le_mul_left' h _) hB
end Set

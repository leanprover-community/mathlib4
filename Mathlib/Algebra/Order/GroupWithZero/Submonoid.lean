/-
Copyright (c) 2021 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Mathlib.Algebra.Group.Submonoid.Defs
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Order.Interval.Set.Defs

/-!
# The submonoid of positive elements
-/

assert_not_exists RelIso Ring

namespace Submonoid
variable (α) [MulZeroOneClass α] [PartialOrder α] [PosMulStrictMono α] [ZeroLEOneClass α]
  [NeZero (1 : α)] {a : α}

/-- The submonoid of positive elements. -/
@[simps] def pos : Submonoid α where
  carrier := Set.Ioi 0
  one_mem' := zero_lt_one
  mul_mem' := mul_pos

variable {α}

@[simp] lemma mem_pos : a ∈ pos α ↔ 0 < a := Iff.rfl

end Submonoid

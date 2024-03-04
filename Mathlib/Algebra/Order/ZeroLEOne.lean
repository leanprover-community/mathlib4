/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro, Johannes Hölzl
-/
import Mathlib.Order.Basic
import Mathlib.Algebra.NeZero

#align_import algebra.order.zero_le_one from "leanprover-community/mathlib"@"07fee0ca54c320250c98bacf31ca5f288b2bcbe2"

/-!
# Typeclass expressing `0 ≤ 1`.
-/

variable {α : Type*}

open Function

/-- Typeclass for expressing that the `0` of a type is less or equal to its `1`. -/
class ZeroLEOneClass (α : Type*) [Zero α] [One α] [LE α] : Prop where
  /-- Zero is less than or equal to one. -/
  zero_le_one : (0 : α) ≤ 1
#align zero_le_one_class ZeroLEOneClass

/-- `zero_le_one` with the type argument implicit. -/
@[simp] lemma zero_le_one [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  ZeroLEOneClass.zero_le_one
#align zero_le_one zero_le_one

/-- `zero_le_one` with the type argument explicit. -/
lemma zero_le_one' (α) [Zero α] [One α] [LE α] [ZeroLEOneClass α] : (0 : α) ≤ 1 :=
  zero_le_one
#align zero_le_one' zero_le_one'

section
variable [Zero α] [One α] [PartialOrder α] [ZeroLEOneClass α] [NeZero (1 : α)]

/-- See `zero_lt_one'` for a version with the type explicit. -/
@[simp] lemma zero_lt_one : (0 : α) < 1 := zero_le_one.lt_of_ne (NeZero.ne' 1)
#align zero_lt_one zero_lt_one

variable (α)

/-- See `zero_lt_one` for a version with the type implicit. -/
lemma zero_lt_one' : (0 : α) < 1 := zero_lt_one
#align zero_lt_one' zero_lt_one'

end

alias one_pos := zero_lt_one
#align one_pos one_pos

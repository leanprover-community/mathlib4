/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Small.Defs

#align_import data.fintype.small from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# All finite types are small.

That is, any `α` with `[Fintype α]` is equivalent to a type in any universe.

-/


universe w v

instance (priority := 100) small_of_fintype (α : Type v) [Fintype α] : Small.{w} α := by
  rw [small_congr (Fintype.equivFin α)]
  infer_instance
#align small_of_fintype small_of_fintype

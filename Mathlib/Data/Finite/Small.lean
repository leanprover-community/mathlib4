/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Markus Himmel
-/
import Mathlib.Data.Finite.Defs
import Mathlib.Logic.Small.Defs

#align_import data.fintype.small from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Finite types are small.
-/

universe u v

section

instance (priority := 100) Finite.small {α : Type v} [Finite α] : Small.{u} α := by
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin α
  exact small_map e
#align small_of_fintype Finite.small

end

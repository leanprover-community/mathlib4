/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import Mathlib.Data.Fintype.Units

#align_import ring_theory.fintype from "leanprover-community/mathlib"@"1126441d6bccf98c81214a0780c73d499f6721fe"

/-!
# Some facts about finite rings
-/


open scoped Classical

theorem card_units_lt (M₀ : Type*) [MonoidWithZero M₀] [Nontrivial M₀] [Fintype M₀] :
    Fintype.card M₀ˣ < Fintype.card M₀ :=
  Fintype.card_lt_of_injective_of_not_mem Units.val Units.ext not_isUnit_zero
#align card_units_lt card_units_lt

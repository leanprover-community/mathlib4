/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
import Mathlib.RingTheory.OreLocalization.Ring
import Mathlib.GroupTheory.OreLocalization.Cardinality

/-!

# Cardinality of Ore localizations of rings

This file contains some results on cardinality of Ore localizations of rings.

-/

universe u

open Cardinal

namespace OreLocalization

variable {R : Type u} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S]

theorem card (hS : S ≤ nonZeroDivisorsRight R) : #(OreLocalization S R) = #R :=
  le_antisymm (card_le S) (mk_le_of_injective (numeratorHom_inj hS))

end OreLocalization

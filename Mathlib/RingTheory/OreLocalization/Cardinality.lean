import Mathlib.Order.OmegaCompletePartialOrder
import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
import Mathlib.Algebra.Module.Defs
import Mathlib.GroupTheory.OreLocalization.Basic
import Mathlib.SetTheory.Cardinal.Defs

/-!
# Cardinality of Ore localizations of rings

This file contains some results on cardinality of Ore localizations of rings.
-/

public section

universe u

open Cardinal

namespace OreLocalization

variable {R : Type u} [Ring R] {S : Submonoid R} [OreLocalization.OreSet S]

theorem cardinalMk (hS : S ≤ nonZeroDivisorsLeft R) : #(OreLocalization S R) = #R :=
  le_antisymm (cardinalMk_le S) (mk_le_of_injective (numeratorHom_inj hS))

end OreLocalization

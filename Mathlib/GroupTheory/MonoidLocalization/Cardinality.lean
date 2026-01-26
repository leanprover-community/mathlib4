import Mathlib.SetTheory.Cardinal.Order

/-!

# Cardinality of localizations of commutative monoids

This file contains some results on cardinality of localizations.

-/

public section

universe u

open Cardinal

namespace Localization

variable {M : Type u} [CommMonoid M] (S : Submonoid M)

@[to_additive]
theorem cardinalMk_le : #(Localization S) ≤ #M :=
  OreLocalization.cardinalMk_le S

end Localization

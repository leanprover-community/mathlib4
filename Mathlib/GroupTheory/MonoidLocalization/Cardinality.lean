/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.GroupTheory.MonoidLocalization.Basic
public import Mathlib.GroupTheory.OreLocalization.Cardinality

@[expose] public section

/-!

# Cardinality of localizations of commutative monoids

This file contains some results on cardinality of localizations.

-/

universe u

open Cardinal

namespace Localization

variable {M : Type u} [CommMonoid M] (S : Submonoid M)

@[to_additive]
theorem cardinalMk_le : #(Localization S) ≤ #M :=
  OreLocalization.cardinalMk_le S

end Localization

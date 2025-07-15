/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
import Mathlib.GroupTheory.Finiteness
import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

/-!
# Localization of a finitely generated submonoid

## TODO

If `Mathlib/GroupTheory/Finiteness.lean` wasn't so heavy, this could move earlier.
-/

open Localization

variable {M : Type*} [CommMonoid M] {S : Submonoid M}

namespace Localization

/-- The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated. -/
@[to_additive "The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated."]
lemma fg [Monoid.FG M] (hS : S.FG) : Monoid.FG <| Localization S := by
  rw [← Monoid.fg_iff_submonoid_fg] at hS; exact Monoid.fg_of_surjective mkHom mkHom_surjective

end Localization

namespace Algebra.GrothendieckGroup

/-- The Grothendieck group of a finitely generated monoid is finitely generated. -/
@[to_additive "The Grothendieck group of a finitely generated monoid is finitely generated."]
instance instFG [Monoid.FG M] : Monoid.FG <| GrothendieckGroup M := fg Monoid.FG.fg_top

end Algebra.GrothendieckGroup

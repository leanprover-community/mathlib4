/-
Copyright (c) 2025 Yaël Dillies, Patrick Luo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Patrick Luo
-/
module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.MonoidLocalization.GrothendieckGroup

set_option doc.verso true
set_option doc.verso.suggestions false

/-!
# Localization of a finitely generated submonoid

## TODO

If `Mathlib/GroupTheory/Finiteness.lean` wasn't so heavy, this could move earlier.
-/

public section

open Localization

variable {M : Type*} [CommMonoid M] {S : Submonoid M}

namespace Localization

/-- The localization of a finitely generated monoid at a finitely generated submonoid is
finitely generated. -/
@[to_additive /-- The localization of a finitely generated monoid at a finitely generated submonoid
is finitely generated. -/]
lemma fg [IsMulFG M] (hS : S.FG) : IsMulFG <| Localization S :=
  IsMulFG.of_surjective mkHom mkHom_surjective

end Localization

namespace Algebra.GrothendieckGroup

/-- The Grothendieck group of a finitely generated monoid is finitely generated. -/
@[to_additive /-- The Grothendieck group of a finitely generated monoid is finitely generated. -/]
instance instFG [IsMulFG M] : IsMulFG <| GrothendieckGroup M := fg inferInstance

end Algebra.GrothendieckGroup

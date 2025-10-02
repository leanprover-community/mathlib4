/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Strict pseudofunctors

In this file we introduce the notion of strict pseudofunctors, which are pseudofunctors such
that `mapId` and `mapComp` are given by `eqToIso _`.

We implement this notion as a typeclass, `Pseudofunctor.IsStrict`.

To a strict pseudofunctor between strict bicategories we can associate a functor between the
underlying categories, see `Pseudofunctor.toFunctor`.

-/

namespace CategoryTheory

open Bicategory

variable {B C : Type*} [Bicategory B] [Bicategory C]

namespace Pseudofunctor

/-- A strict pseudofunctor between bicategories is one such that `mapId` and `mapComp` are
given by `eqToIso _`. -/
class IsStrict (F : Pseudofunctor B C) : Prop where
  map_id : ∀ (b : B), F.map (𝟙 b) = 𝟙 (F.obj b) := by cat_disch
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), F.map (f ≫ g) = F.map f ≫ F.map g := by
    cat_disch
  mapId : ∀ (b : B), F.mapId b = eqToIso (map_id b) := by cat_disch
  mapComp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), F.mapComp f g = eqToIso (map_comp f g) := by
    cat_disch

section

variable [Strict B] [Strict C]

/-- A strict pseudofunctor between strict bicategories induces a functor on the underlying
categories. -/
def toFunctor (F : Pseudofunctor B C) [Pseudofunctor.IsStrict F] : Functor B C where
  obj := F.obj
  map := F.map
  map_id := IsStrict.map_id
  map_comp := IsStrict.map_comp

end

end Pseudofunctor

end CategoryTheory

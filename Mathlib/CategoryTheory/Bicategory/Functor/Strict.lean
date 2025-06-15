/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!
# Strict functors

In this file we define strict functors between bicategories, which are pseudofunctors such
that `mapId` and `mapComp` are given by `eqToIso _`.

Strict

-/

namespace CategoryTheory

open Category Bicategory

universe w₁ w₂ w₃ v₁ v₂ v₃ u₁ u₂ u₃

variable {B : Type* } [Bicategory B] {C : Type*} [Bicategory C]
--variable {D : Type u₃} [Bicategory.{w₃, v₃} D]

namespace Pseudofunctor

/-- A strict pseudofunctor between bicategories is one such that `mapId` and `mapComp` are
given by `eqToIso _`. -/
class IsStrict (F : Pseudofunctor B C) : Prop where
  map_id : ∀ (b : B), F.map (𝟙 b) = 𝟙 (F.obj b) := by aesop_cat
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), F.map (f ≫ g) = F.map f ≫ F.map g := by
    aesop_cat
  mapId : ∀ (b : B), F.mapId b = eqToIso (map_id b) := by aesop_cat
  mapComp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), F.mapComp f g = eqToIso (map_comp f g) := by
    aesop_cat

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

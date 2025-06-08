/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.EqToHom

/-!

# Sub-bicategories

In this file we develop API for constructing a locally full sub-bicategory of a
bicategory.

Ideas:
- Should have: inclusion of objects & inclusion of morphisms


-/

namespace CategoryTheory.Bicategory

open Category

universe w v u w₁ v₁ u₁

variable {B : Type*} (C : Type*) [Bicategory C] (F : B → C)

/-- `InducedCategory D F`, where `F : C → D`, is a typeclass synonym for `C`,
which provides a category structure so that the morphisms `X ⟶ Y` are the morphisms
in `D` from `F X` to `F Y`.
-/
@[nolint unusedArguments]
def InducedBicategory (_F : B → C) : Type _ :=
  B

namespace InducedBicategory

variable {C}

instance hasCoeToSort {α : Sort*} [CoeSort C α] : CoeSort (InducedBicategory C F) α :=
  ⟨fun c => F c⟩

instance bicategory : Bicategory (InducedBicategory C F) where
  Hom X Y := F X ⟶ F Y
  id X := 𝟙 (F X)
  comp f g := f ≫ g
  whiskerLeft := whiskerLeft
  whiskerRight := whiskerRight
  associator := associator
  leftUnitor := leftUnitor
  rightUnitor := rightUnitor
  whisker_exchange := whisker_exchange
  pentagon := pentagon
  triangle := triangle

section

attribute [-simp] eqToIso_refl

/-- The forgetful functor from an induced category to the original category,
forgetting the extra data.
-/
@[simps]
def inducedPseudofunctor : Pseudofunctor (InducedBicategory C F) C where
  obj := F
  map f := f
  map₂ η := η
  mapId b := eqToIso rfl
  mapComp f g := eqToIso rfl

-- TODO: add IsStrict when possible

end

end InducedBicategory

end CategoryTheory.Bicategory

/-
Copyright (c) 2025 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/
import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor

/-!

# Induced bicategories

In this file we develop API for constructing a full sub-bicategory of a bicategory.

-/

namespace CategoryTheory.Bicategory

variable {B : Type*} (C : Type*) [Bicategory C] (F : B → C)

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`. This is given
a bicategory structure where the 1-morphisms `X ⟶ Y` are the 1-morphisms in `C` from `F X` to
`F Y`, and the 2-morphisms `f ⟶ g` are also the 2-morphisms in `C` from `f` to `g`.
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

/-- The forgetful functor from an induced bicategory to the original bicategory,
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

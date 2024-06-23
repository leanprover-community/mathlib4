/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.EqToHom

/-!

# Sub-bicategories

In this file we develop API for constructing a locally full sub-bicategory of a
bicategory.

Ideas:
- Should have: inclusion of objects & inclusion of morphisms


-/

namespace CategoryTheory

namespace Bicategory

open Category

open scoped Bicategory

universe w v u w₁ v₁ u₁

variable (B : Type u) [CategoryStruct.{v} B] (C : Type u₁) [Bicategory.{w₁, v₁} C]

-- TODO: F' needs to respect compositions!! (i.e. F needs to be a prefunctor)
-- TODO: maybe not...?

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`,
which provides a bicategory structure so that the 2-morphisms `X ⟶ Y` are the 2-morphisms
in `C` from `F X` to `F Y`.
-/

structure FunctorStruct extends Prefunctor B C where
  map_comp : ∀ {a b c : B} (f : a ⟶ b) (g : b ⟶ c), map (f ≫ g) = map f ≫ map g
  map_id : ∀ {a : B}, map (𝟙 a) = 𝟙 (obj a)

variable {B}
variable (F : FunctorStruct B C)

def InducedBicategory (_F : FunctorStruct B C) : Type u := B
  -- respects associators etc



namespace InducedBicategory

variable {C}

instance hasCoeToSort {α : Sort*} [CoeSort C α] :
    CoeSort (InducedBicategory C F) α :=
  ⟨fun c ↦ F.obj c⟩

instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom a b := InducedCategory (F.obj a ⟶ F.obj b) (F.map (X := a) (Y := b))
  id a := let a' : B := a; 𝟙 a'
  comp {a b c} f g := by
    let a' : B := a
    let b' : B := b
    let f' : a' ⟶ b' := f
    -- TODO: dangerous?
    apply f' ≫ g

-- TODO: fix universe
instance bicategory : Bicategory.{w₁, v} (InducedBicategory C F) where
  toCategoryStruct := categoryStruct F
  homCategory a b := InducedCategory.category (F.map (X := a) (Y:=b))
  -- Need "F" "PseudoStruct" here (so mapId + mapComp + coherences + no 2-morphisms)
  whiskerLeft {a b c} f {g h} η := by
    apply eqToHom (F.map_comp f g) ≫ ((F.map f) ◁ η) ≫ eqToHom (F.map_comp f h).symm
  whiskerRight {a b c f g} η h := by
    apply eqToHom (F.map_comp f h) ≫ (η ▷(F.map h)) ≫ eqToHom (F.map_comp g h).symm
  associator f g h := by
    apply eqToIso (show
        F.map ((f ≫ g) ≫ h) = (F.map f ≫ F.map g) ≫ F.map h by simp [F.map_comp]) ≪≫
      α_ (F.map f) (F.map g) (F.map h) ≪≫ eqToIso (show F.map f ≫ F.map g ≫ F.map h = F.map (f ≫ g ≫ h) by simp [F.map_comp])
  leftUnitor := sorry
  rightUnitor := sorry
  whiskerLeft_id := sorry
  whiskerLeft_comp := sorry
  id_whiskerLeft := sorry
  comp_whiskerLeft := sorry
  id_whiskerRight := sorry
  comp_whiskerRight := sorry
  whiskerRight_id := sorry
  whiskerRight_comp := sorry
  whisker_assoc := sorry
  whisker_exchange := sorry
  pentagon := sorry
  triangle := sorry
  -- -- TODO: bad definition here?
  -- toCategoryStruct := by unfold InducedBicategory; infer_instance

end InducedBicategory

end Bicategory

end CategoryTheory

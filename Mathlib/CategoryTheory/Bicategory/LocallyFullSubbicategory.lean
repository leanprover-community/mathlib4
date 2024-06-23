/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.Basic
import Mathlib.CategoryTheory.FullSubcategory

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

variable {B : Type u} [CategoryStruct.{v} B] (C : Type u₁) [Bicategory.{w₁, v₁} C]

-- TODO: F' needs to respect compositions!! (i.e. F needs to be a prefunctor)
-- TODO: maybe not...?
variable (F : Prefunctor B C)

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`,
which provides a bicategory structure so that the 2-morphisms `X ⟶ Y` are the 2-morphisms
in `C` from `F X` to `F Y`.
-/
-- TODO: make this a structure...
structure InducedBicategory (_F : Prefunctor B C) : Type u :=
  as : B

structure InducedBicategory' where
  obj : Type u
  categoryStruct : CategoryStruct.{v} obj
  -- TODO: hom as above or sth
  F : Prefunctor obj C
  -- commute w/ comp
  mapComp : ∀ {a b c : obj} (f : a ⟶ b) (g : b ⟶ c), F.map (f ≫ g) ≅ F.map f ≫ F.map g
  mapId : ∀ {a : obj}, F.map (𝟙 a) ≅ 𝟙 (F.obj a)
  -- respects associators etc



namespace InducedBicategory

variable {C}

instance hasCoeToSort {α : Sort*} [CoeSort C α] :
    CoeSort (InducedBicategory C F) α :=
  ⟨fun c ↦ F.obj c.1⟩

instance categoryStruct : CategoryStruct (InducedBicategory C F) where
  Hom a b := InducedCategory (F.obj a.1 ⟶ F.obj b.1) (F.map (X := a.1) (Y := b.1))
  id a := 𝟙 a.1
  comp f g := f ≫ g

-- TODO: fix universe
instance bicategory : Bicategory.{w₁, v} (InducedBicategory C F) where
  toCategoryStruct := categoryStruct F
  homCategory a b := InducedCategory.category (F.map (X := a.1) (Y:=b.1))
  -- Need "F" "PseudoStruct" here (so mapId + mapComp + coherences + no 2-morphisms)
  whiskerLeft {a b c} f {g h} η := ((F.map f) ◁ η)
  whiskerRight := sorry
  associator f g h := α_ (F.map f) (F.map g) (F.map h)
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

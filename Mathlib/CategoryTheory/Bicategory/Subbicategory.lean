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
-- NEED some comparison of Hom's here too!
variable (F : B → C) --(F' : (a : B) × (b : B) × (a ⟶ b) → (F a ⟶ F b))

/-- `InducedBicategory B C`, where `F : B → C`, is a typeclass synonym for `B`,
which provides a bicategory structure so that the 2-morphisms `X ⟶ Y` are the 2-morphisms
in `C` from `F X` to `F Y`.
-/
def InducedBicategory (_F : B → C) : Type u :=
  B

variable {C}

instance InducedBicategory.hasCoeToSort {α : Sort*} [CoeSort C α] :
    CoeSort (InducedBicategory C F) α :=
  ⟨fun c ↦ F c⟩

-- TODO: fix universe
instance InducedBicategory.bicategory : Bicategory.{w₁, v} (InducedBicategory C F) where
  toCategoryStruct := by unfold InducedBicategory; infer_instance
  homCategory := sorry
  whiskerLeft := sorry
  whiskerRight := sorry
  associator := sorry
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

end Bicategory

end CategoryTheory

/-
Copyright (c) 2024 Calle Sönne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Calle Sönne
-/

import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
import Mathlib.CategoryTheory.Bicategory.Opposites
import Mathlib.CategoryTheory.Category.Cat

/-!
# 2-Yoneda embedding

-/

namespace CategoryTheory

open Category Bicategory

open Bicategory

universe w₁ v₁ u₁ w v u

/-- A `SmallCategory` has objects and morphisms in the same universe level.
-/
abbrev LocallySmallBicategory (B : Type u₁) : Type _ := Bicategory.{v₁, v₁, u₁} B

namespace Bicategory

-- TODO: small when?!
variable {B : Type u₁} [LocallySmallBicategory.{v₁} B]

#check precomp

def representable (x : B) : Pseudofunctor Bᴮᵒᵖ Cat.{v₁, v₁} := {
  obj := fun y => Cat.of (y ⟶ ⟨x⟩)
  map := fun {a b} f => (precomp _ f)
  map₂ := sorry,
  mapId := sorry,
  mapComp := sorry,
  map₂_id := sorry,
  map₂_comp := sorry,
  map₂_whisker_left := sorry,
  map₂_whisker_right := sorry,
  map₂_associator := sorry,
  map₂_left_unitor := sorry,
  map₂_right_unitor := sorry
}

-- def yoneda : Pseudofunctor B (Pseudofunctor Bᴮᵒᵖ Cat.{v₁, v₁}) where
--   obj x := {
--     obj := fun y => Cat.of (y ⟶ ⟨x⟩)
--     map := fun {a b} f => (precomp _ f)
--     map₂ := sorry
--     mapId := sorry
--     mapComp := sorry
--     map₂_id := sorry
--     map₂_comp := sorry
--     map₂_whisker_left := sorry
--     map₂_whisker_right := sorry
--     map₂_associator := sorry
--     map₂_left_unitor := sorry
--     map₂_right_unitor := sorry
--   }
--   map := sorry
--   map₂ := sorry
--   mapId := sorry
--   mapComp := sorry
--   map₂_id := sorry
--   map₂_comp := sorry
--   map₂_whisker_left := sorry
--   map₂_whisker_right := sorry
--   map₂_associator := sorry
--   map₂_left_unitor := sorry
--   map₂_right_unitor := sorry

end Bicategory

end CategoryTheory

end Bicategory

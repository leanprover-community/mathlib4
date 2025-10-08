/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# Adjunctions in `Cat`

-/

universe v u

namespace CategoryTheory

open Bicategory

variable {C D : Type u} [Category C] [Category D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

attribute [local simp] bicategoricalComp Cat.associator_hom_app Cat.associator_inv_app
  Cat.leftUnitor_hom_app Cat.leftUnitor_inv_app Cat.rightUnitor_hom_app Cat.rightUnitor_inv_app
  Functor.toCatHom

abbrev Adjunction.toCat : Bicategory.Adjunction F.toCatHom G.toCatHom where
  unit := adj.unit
  counit := adj.counit

end CategoryTheory

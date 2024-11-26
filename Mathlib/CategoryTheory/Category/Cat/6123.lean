/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.ConnectedComponents

universe v u
namespace CategoryTheory.Cat

variable (X : Type u) (C : Cat)

private def typeToCatObjectsAdjHomEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun f x := f.obj ⟨x⟩
  invFun := Discrete.functor
  left_inv F := sorry
  right_inv _ := sorry

private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom
  map_id := sorry
  map_comp := sorry

/-- `typeToCat : Type ⥤ Cat` is left adjoint to `Cat.objects : Cat ⥤ Type` -/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects :=
  Adjunction.mk' {
    homEquiv := typeToCatObjectsAdjHomEquiv
    unit := sorry
    counit := {
      app := typeToCatObjectsAdjCounitApp
      naturality := sorry }
    homEquiv_counit := by
      intro X Y g
      simp_all only [typeToCat_obj, Functor.id_obj, typeToCat_map, of_α, id_eq]
      rfl }

/-- The connected components functor -/
def connectedComponents : Cat.{v, u} ⥤ Type u where
  obj C := ConnectedComponents C
  map F := Functor.mapConnectedComponents F
  map_id _ := sorry
  map_comp _ _ := sorry

/-- `typeToCat : Type ⥤ Cat` is right adjoint to `connectedComponents : Cat ⥤ Type` -/
def connectedComponentsTypeToCatAdj : connectedComponents ⊣ typeToCat :=
  Adjunction.mk' {
    homEquiv := fun C X ↦ ConnectedComponents.typeToCatHomEquiv C X
    unit :=
      { app:= fun C  ↦ ConnectedComponents.functorToDiscrete _ (𝟙 (connectedComponents.obj C))
        naturality := by
          intro X Y f
          simp_all only [Functor.id_obj, Functor.comp_obj, typeToCat_obj, Functor.id_map,
            Functor.comp_map, typeToCat_map, of_α, id_eq]
          rfl }
    counit := sorry
    homEquiv_counit := sorry }

end CategoryTheory.Cat

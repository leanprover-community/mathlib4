/-
Copyright (c) 2024 Nicolas Rolland. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolas Rolland
-/
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Adjunction.Basic
/-!
# Adjunctions related to Cat, the category of categories

The embedding `Type ⥤ Cat` has a right adjoint `Cat.objects` mapping
each category to its set of objects.


## Notes
All this could be made with 2-functors

## TODO
The embedding `Type ⥤ Cat` has a left adjoint `Cat.connectedComponents` mapping
each category to its set of connected components.
-/

universe u
namespace CategoryTheory

variable (X : Type u) (C : Cat)

private def homEquiv : (typeToCat.obj X ⟶ C) ≃ (X ⟶ Cat.objects.obj C) where
  toFun f x := f.obj ⟨x⟩
  invFun := Discrete.functor
  left_inv F := Functor.ext (fun _ ↦ rfl)
                            (fun⟨_⟩ ⟨_⟩ f => by
                                    obtain rfl := Discrete.eq_of_hom f
                                    simp)
  right_inv := fun _ ↦ funext (fun _ => rfl)

private def typeToCatObjectsAdjCounitApp : (Cat.objects ⋙ typeToCat).obj C ⥤ C where
  obj := Discrete.as
  map := eqToHom ∘ Discrete.eq_of_hom

/-- typeToCat : Type ⥤ Cat is left adjoint to Cat.objects : Cat ⥤ Type -/
def typeToCatObjectsAdj : typeToCat ⊣ Cat.objects where
  homEquiv  := homEquiv
  unit : 𝟭 (Type u) ⟶ typeToCat ⋙ Cat.objects := { app:= fun _  ↦ Discrete.mk }
  counit : Cat.objects ⋙ typeToCat ⟶ 𝟭 Cat := {
    app := typeToCatObjectsAdjCounitApp
    naturality := fun _ _ _  ↦  Functor.hext (fun _ ↦ rfl)
      (by intro ⟨_⟩ ⟨_⟩ f
          obtain rfl := Discrete.eq_of_hom f
          aesop_cat ) }

end CategoryTheory

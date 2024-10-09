/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Presheaf

/-!
# Change of presheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R`
attached to a morphism of presheaves of rings `α : R ⟶ R'`.

-/

universe v v' u u'

open CategoryTheory

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] {R R' : Cᵒᵖ ⥤ RingCat.{u}}

/-- The restriction of scalars of presheaves of modules, on objects. -/
@[simps]
noncomputable def restrictScalarsObj (M' : PresheafOfModules.{v} R') (α : R ⟶ R') :
    PresheafOfModules R where
  obj := fun X ↦ (ModuleCat.restrictScalars (α.app X)).obj (M'.obj X)
  map := fun {X Y} f ↦
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x ↦ (M'.map_smul f (α.app _ r) x).trans (by
        have eq := RingHom.congr_fun (α.naturality f) r
        dsimp at eq
        rw [← eq]
        rfl ) }

/-- The restriction of scalars functor `PresheafOfModules R' ⥤ PresheafOfModules R`
induced by a morphism of presheaves of rings `R ⟶ R'`. -/
@[simps]
noncomputable def restrictScalars (α : R ⟶ R') :
    PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R where
  obj M' := M'.restrictScalarsObj α
  map φ' :=
    { app := fun X ↦ (ModuleCat.restrictScalars (α.app X)).map (Hom.app φ' X)
      naturality := fun {X Y} f ↦ by
        ext x
        exact naturality_apply φ' f x }

instance (α : R ⟶ R') : (restrictScalars.{v} α).Additive where

instance : (restrictScalars (𝟙 R)).Full := inferInstanceAs (𝟭 _).Full

instance (α : R ⟶ R') : (restrictScalars α).Faithful where
  map_injective h := (toPresheaf R').map_injective ((toPresheaf R).congr_map h)

/-- The isomorphism `restrictScalars α ⋙ toPresheaf R ≅ toPresheaf R'` for any
morphism of presheaves of rings `α : R ⟶ R'`. -/
noncomputable def restrictScalarsCompToPresheaf (α : R ⟶ R') :
    restrictScalars.{v} α ⋙ toPresheaf R ≅ toPresheaf R' := Iso.refl _

end PresheafOfModules

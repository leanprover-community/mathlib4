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
noncomputable def restrictScalarsBundledCore (M' : PresheafOfModules R') (α : R ⟶ R') :
    BundledCorePresheafOfModules R where
  obj X := (ModuleCat.restrictScalars (α.app X)).obj (M'.obj X)
  map {X Y} f :=
    { toFun := M'.map f
      map_add' := map_add _
      map_smul' := fun r x ↦ by
        have eq := RingHom.congr_fun (α.naturality f) r
        apply (M'.map_smul f (α.app _ r) x).trans
        dsimp at eq ⊢
        rw [← eq]
        rfl }
  map_id X := by
    ext x
    exact LinearMap.congr_fun (M'.map_id X) x
  map_comp f g := by
    ext x
    exact LinearMap.congr_fun (M'.map_comp f g) x

/-- The restriction of scalars functor `PresheafOfModules R' ⥤ PresheafOfModules R`
induced by a morphism of presheaves of rings `R ⟶ R'`. -/
@[simps]
noncomputable def restrictScalars (α : R ⟶ R') :
    PresheafOfModules.{v} R' ⥤ PresheafOfModules.{v} R where
  obj M' := (M'.restrictScalarsBundledCore α).toPresheafOfModules
  map {M₁' M₂'} φ :=
    { hom := φ.hom
      map_smul := fun X r ↦ φ.map_smul X (α.app _ r) }

end PresheafOfModules

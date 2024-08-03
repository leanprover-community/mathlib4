/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-!
# Change of sheaf of rings

In this file, we define the restriction of scalars functor
`restrictScalars α : SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R`
attached to a morphism of sheaves of rings `α : R ⟶ R'`.

-/

universe v v' u u'

open CategoryTheory

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}

namespace SheafOfModules

variable {R R' : Sheaf J RingCat.{u}} (α : R ⟶ R')

/-- The restriction of scalars functor `SheafOfModules R' ⥤ SheafOfModules R`
induced by a morphism of sheaves of rings `R ⟶ R'`. -/
@[simps]
noncomputable def restrictScalars :
    SheafOfModules.{v} R' ⥤ SheafOfModules.{v} R where
  obj M' :=
    { val := (PresheafOfModules.restrictScalars α.val).obj M'.val
      isSheaf := M'.isSheaf }
  map φ := { val := (PresheafOfModules.restrictScalars α.val).map φ.val }

instance : (restrictScalars.{v} α).Additive where

end SheafOfModules

namespace PresheafOfModules

variable {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {M₁ M₂ : PresheafOfModules.{v} R'} (hM₂ : Presheaf.IsSheaf J M₂.presheaf)
  [Presheaf.IsLocallySurjective J α]

/-- The functor `PresheafOfModules.restrictScalars α` induces bijection on
morphisms if `α` is locally surjective and the target presheaf is a sheaf. -/
noncomputable def restrictHomEquivOfIsLocallySurjective :
    (M₁ ⟶ M₂) ≃ ((restrictScalars α).obj M₁ ⟶ (restrictScalars α).obj M₂) where
  toFun f := (restrictScalars α).map f
  invFun g :=
    { hom := g.hom
      map_smul := fun X r' m => by
        apply hM₂.isSeparated _ _ (Presheaf.imageSieve_mem J α r')
        rintro Y p ⟨r : R.obj _, hr⟩
        erw [M₂.map_smul, ← NatTrans.naturality_apply g.hom p.op m,
          ← hr, ← g.map_smul _ r (M₁.presheaf.map p.op m),
          ← NatTrans.naturality_apply g.hom p.op (r' • m),
          M₁.map_smul p.op r' m, ← hr]
        rfl }
  left_inv _ := rfl
  right_inv _ := rfl

end PresheafOfModules

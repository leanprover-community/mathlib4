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
      isSheaf := (Presheaf.isSheaf_of_iso_iff
        { hom.app X := AddCommGrp.ofHom <|
            (Module.RestrictScalars.outAddEquiv _ _).symm.toAddMonoidHom
          inv.app X := AddCommGrp.ofHom <|
            (Module.RestrictScalars.outAddEquiv _ _).toAddMonoidHom }).mp
        M'.isSheaf }
  map φ := { val := (PresheafOfModules.restrictScalars α.val).map φ.val }

instance : (restrictScalars.{v} α).Additive where

end SheafOfModules

namespace PresheafOfModules

open ModuleCat.restrictScalars

variable {R R' : Cᵒᵖ ⥤ RingCat.{u}} (α : R ⟶ R')
  {M₁ M₂ : PresheafOfModules.{v} R'}

/-- The functor `PresheafOfModules.restrictScalars α` induces bijections on
morphisms if `α` is locally surjective and the target presheaf is a sheaf. -/
noncomputable def restrictHomEquivOfIsLocallySurjective
    (hM₂ : Presheaf.IsSheaf J M₂.presheaf) [Presheaf.IsLocallySurjective J α] :
    (M₁ ⟶ M₂) ≃ ((restrictScalars α).obj M₁ ⟶ (restrictScalars α).obj M₂) where
  toFun f := (restrictScalars α).map f
  invFun g := homMk ((restrictScalarsCompToPresheaf α).inv.app _ ≫ ((toPresheaf R).map g) ≫
  (restrictScalarsCompToPresheaf α).hom.app _) (fun X r' m ↦ by
    apply hM₂.isSeparated _ _ (Presheaf.imageSieve_mem J α r')
    rintro Y p ⟨r : R.obj _, hr⟩
    have hg : ∀ (z : M₁.obj X), out _ (g.app _ (into _ (out _ (M₁.map p.op z)))) =
        out _ (M₂.map p.op (out _ (g.app X (into _ z)))) := fun z ↦ by
          have := congr_arg (out _) (congr_arg (out _)
            (congr_fun ((forget _).congr_map (g.naturality p.op)) (into _ z)))
          dsimp at this ⊢
          exact this
    change out _ (M₂.map p.op (out _ (g.app X (into _ (r' • m))))) =
      out _ (M₂.map p.op (r' • (out _ (g.app X (into _ m)))))
    dsimp at hg ⊢
    rw [← hg, map_smul, out_into, map_smul, out_into, ← hr, ← hg, ← smul_def', map_smulₛₗ,
        RingHom.id_apply, map_smulₛₗ])
  left_inv _ := rfl
  right_inv _ := rfl

end PresheafOfModules

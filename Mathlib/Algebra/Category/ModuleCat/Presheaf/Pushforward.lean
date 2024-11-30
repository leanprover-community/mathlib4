/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings

/-!
# Pushforward of presheaves of modules

If `F : C ⥤ D`, the precomposition `F.op ⋙ _` induces a functor from presheaves
over `D` to presheaves over `C`. When `R : Dᵒᵖ ⥤ RingCat`, we define the
induced functor `pushforward₀ : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R)`
on presheaves of modules.

In case we have a morphism of presheaves of rings `S ⟶ F.op ⋙ R`, we also construct
a functor `pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S`.

-/

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace PresheafOfModules

variable (F : C ⥤ D)

/-- The pushforward functor on presheaves of modules for a functor `F : C ⥤ D` and
`R : Dᵒᵖ ⥤ RingCat`. On the underlying presheaves of abelian groups, it is induced
by the precomposition with `F.op`. -/
def pushforward₀ (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R) where
  obj M :=
    { obj := fun X ↦ ModuleCat.of _ (M.obj (F.op.obj X))
      map := fun {X Y} f ↦ M.map (F.op.map f)
      map_id := fun X ↦ by
        ext x
        exact (M.congr_map_apply (F.op.map_id X) x).trans (by simp)
      map_comp := fun f g ↦ by
        ext x
        exact (M.congr_map_apply (F.op.map_comp f g) x).trans (by simp) }
  map {M₁ M₂} φ := { app := fun X ↦ φ.app _ }

/-- The pushforward of presheaves of modules commutes with the forgetful functor
to presheaves of abelian groups. -/
def pushforward₀CompToPresheaf (R : Dᵒᵖ ⥤ RingCat.{u}) :
    pushforward₀.{v} F R ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

variable {F}
variable {R : Dᵒᵖ ⥤ RingCat.{u}} {S : Cᵒᵖ ⥤ RingCat.{u}} (φ : S ⟶ F.op ⋙ R)

attribute [local simp] pushforward₀ in
/-- The pushforward functor `PresheafOfModules R ⥤ PresheafOfModules S` induced by
a morphism of presheaves of rings `S ⟶ F.op ⋙ R`. -/
@[simps! obj_obj]
noncomputable def pushforward : PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} S :=
  pushforward₀ F R ⋙ restrictScalars φ

/-- The pushforward of presheaves of modules commutes with the forgetful functor
to presheaves of abelian groups. -/
noncomputable def pushforwardCompToPresheaf :
    pushforward.{v} φ ⋙ toPresheaf _ ≅ toPresheaf _ ⋙ (whiskeringLeft _ _ _).obj F.op :=
  Iso.refl _

@[simp]
lemma pushforward_obj_map_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (α := (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop))))
        (β := fun _ ↦ (ModuleCat.restrictScalars (φ.app Y)).obj
          (M.obj (Opposite.op (F.obj Y.unop)))) (((pushforward φ).obj M).map f) m =
        M.map (F.map f.unop).op m := rfl

@[simp]
lemma pushforward_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (α := (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop))))
      (β := fun _ ↦ (ModuleCat.restrictScalars (φ.app X)).obj
        (N.obj (Opposite.op (F.obj X.unop))))
      (((pushforward φ).map α).app X) m = α.app (Opposite.op (F.obj X.unop)) m := rfl

end PresheafOfModules

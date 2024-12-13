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

open ModuleCat.restrictScalars

variable (F : C ⥤ D)

set_option maxHeartbeats 400000 in
-- After squeezing simps, this costs 209009 heartbeats...
/-- The pushforward functor on presheaves of modules for a functor `F : C ⥤ D` and
`R : Dᵒᵖ ⥤ RingCat`. On the underlying presheaves of abelian groups, it is induced
by the precomposition with `F.op`. -/
def pushforward₀ (R : Dᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} R ⥤ PresheafOfModules.{v} (F.op ⋙ R) where
  obj M :=
    { obj := fun X ↦ ModuleCat.of _ (M.obj (F.op.obj X))
      map := fun {X Y} f ↦ M.map (F.op.map f)
      map_id := fun X ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        exact (M.congr_map_apply (F.op.map_id X) x).trans (by
          simp only [Functor.op_obj, Functor.op_map, unop_id, map_id,
            ModuleCat.restrictScalarsId'_inv_app, ModuleCat.restrictScalarsId'App_inv_apply,
            out_into, Functor.comp_obj, Functor.comp_map, ModuleCat.of_coe])
      map_comp := fun f g ↦ by
        refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
        exact (M.congr_map_apply (F.op.map_comp f g) x).trans (by
          ext
          simp only [Functor.op_obj, Functor.op_map, unop_comp, map_comp,
            ModuleCat.restrictScalarsComp'_inv_app, ModuleCat.restrictScalarsComp'App,
            ModuleCat.hom_comp, LinearEquiv.toModuleIso_inv_hom, LinearMap.coe_comp,
            LinearEquiv.coe_coe, AddEquiv.coe_toLinearEquiv_symm, AddEquiv.symm_mk, AddEquiv.coe_mk,
            Equiv.coe_fn_symm_mk, coe_map, Function.comp_apply, out_into, Functor.comp_obj,
            ModuleCat.of_coe, Functor.comp_map]) }
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
  Functor.associator _ _ _ ≪≫
    (isoWhiskerLeft _ (restrictScalarsCompToPresheaf _)) ≪≫
    (pushforward₀CompToPresheaf _ _)

lemma pushforward_obj_map_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      (((pushforward φ).obj M).map f).hom m =
        into _ (into _ (out _ (M.map (F.map f.unop).op (out _ m)))) := rfl

/-- `@[simp]`-normal form of `pushforward_obj_map_apply`. -/
@[simp]
lemma pushforward_obj_map_apply' (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_]
          ↑((ModuleCat.restrictScalars (S.map f)).obj ((ModuleCat.restrictScalars _).obj _)))
        (((pushforward φ).obj M).map f).hom m =
          into _ (into _ (out _ (M.map (F.map f.unop).op (out _ m)))) := rfl

lemma pushforward_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    (((pushforward φ).map α).app X).hom m =
      into _ (α.app (Opposite.op (F.obj X.unop)) (out _ m)) := rfl

/-- `@[simp]`-normal form of `pushforward_map_app_apply`. -/
@[simp]
lemma pushforward_map_app_apply' {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X)).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_] ↑((ModuleCat.restrictScalars _).obj _))
      (((pushforward φ).map α).app X).hom m =
        into _ (α.app (Opposite.op (F.obj X.unop)) (out _ m)) := rfl

end PresheafOfModules

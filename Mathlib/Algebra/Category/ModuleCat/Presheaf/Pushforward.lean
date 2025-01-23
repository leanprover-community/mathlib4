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

universe v v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ u

open CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E] {E' : Type u₄} [Category.{v₄} E']

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
        refine ModuleCat.hom_ext
          -- Work around an instance diamond for `restrictScalarsId'`
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
        exact (M.congr_map_apply (F.op.map_id X) x).trans (by simp)
      map_comp := fun f g ↦ by
        refine ModuleCat.hom_ext
          -- Work around an instance diamond for `restrictScalarsId'`
          (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ (fun x => ?_))
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

lemma pushforward_obj_map_apply (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

/-- `@[simp]`-normal form of `pushforward_obj_map_apply`. -/
@[simp]
lemma pushforward_obj_map_apply' (M : PresheafOfModules.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
      DFunLike.coe
        (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_]
          ↑((ModuleCat.restrictScalars (S.map f).hom).obj ((ModuleCat.restrictScalars _).obj _)))
        (((pushforward φ).obj M).map f).hom m = M.map (F.map f.unop).op m := rfl

lemma pushforward_map_app_apply {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

/-- `@[simp]`-normal form of `pushforward_map_app_apply`. -/
@[simp]
lemma pushforward_map_app_apply' {M N : PresheafOfModules.{v} R} (α : M ⟶ N) (X : Cᵒᵖ)
    (m : (ModuleCat.restrictScalars (φ.app X).hom).obj (M.obj (Opposite.op (F.obj X.unop)))) :
    DFunLike.coe
      (F := ↑((ModuleCat.restrictScalars _).obj _) →ₗ[_] ↑((ModuleCat.restrictScalars _).obj _))
      (((pushforward φ).map α).app X).hom m = α.app (Opposite.op (F.obj X.unop)) m := rfl

section

variable (R) in
noncomputable def pushforwardId :
    pushforward.{v} (S := R) (F := 𝟭 _) (𝟙 R) ≅ 𝟭 _ :=
  Iso.refl _

section

variable {T : Eᵒᵖ ⥤ RingCat.{u}} {G : D ⥤ E} (ψ : R ⟶ G.op ⋙ T)

noncomputable def pushforwardComp :
  pushforward.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ≅
    pushforward.{v} ψ ⋙ pushforward.{v} φ :=
  Iso.refl _

variable {T' : E'ᵒᵖ ⥤ RingCat.{u}} {G' : E ⥤ E'} (ψ' : T ⟶ G'.op ⋙ T')

lemma pushforward_assoc :
    pushforwardComp.{v} (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ' ≪≫
      isoWhiskerLeft _ (pushforwardComp.{v} φ ψ) =
    pushforwardComp.{v} (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ') ≪≫
      isoWhiskerRight (pushforwardComp.{v} ψ ψ') _ ≪≫
        Functor.associator _ _ _ := by ext; rfl

lemma pushforward_hom_app_assoc (M : PresheafOfModules.{v} T') :
    (pushforwardComp (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ').hom.app M ≫
      (pushforwardComp φ ψ).hom.app _ =
      (pushforwardComp (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ')).hom.app M ≫
      (pushforward φ).map ((pushforwardComp ψ ψ').hom.app _) := by
  rfl

lemma pushforward_inv_app_assoc (M : PresheafOfModules.{v} T') :
    (pushforwardComp φ ψ).inv.app _ ≫
      (pushforwardComp (F := F ⋙ G) (φ ≫ whiskerLeft F.op ψ) ψ').inv.app M =
    (pushforward φ).map ((pushforwardComp ψ ψ').inv.app _) ≫
      (pushforwardComp (G := G ⋙ G') φ (ψ ≫ whiskerLeft G.op ψ')).inv.app M := rfl

end

lemma pushforward_id_comp :
    pushforwardComp.{v} (F := 𝟭 C) (𝟙 S) φ = (Functor.rightUnitor _).symm ≪≫
      isoWhiskerLeft (pushforward.{v} φ) (pushforwardId S).symm := by ext; rfl

lemma pushforward_comp_id :
    pushforwardComp.{v} (G := 𝟭 _) φ (𝟙 R) = (Functor.leftUnitor _).symm ≪≫
      isoWhiskerRight (pushforwardId R).symm (pushforward.{v} φ) := by ext; rfl

end

end PresheafOfModules

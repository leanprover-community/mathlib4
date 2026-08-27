/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing

/-!
# Modules over presheaves and sheaves of commutative rings

This file provides short names for categories and functors obtained from a presheaf or
sheaf of commutative rings by forgetting to rings. In particular, these names avoid
repeatedly writing the relevant forgetful functor or `sheafCompose`.
-/

@[expose] public noncomputable section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor Limits

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

abbrev over (M : PresheafOfModulesOfCommRing.{v} R) (X : C) :
    PresheafOfModulesOfCommRing.{v} ((Over.forget X).op ⋙ R) :=
  (pushforward.{v} (𝟙 _)).obj M

abbrev overHom {M N : PresheafOfModulesOfCommRing.{v} R} (φ : M ⟶ N)
    (X : C) : M.over X ⟶ N.over X := (pushforward.{v} (𝟙 _)).map φ

variable (F : (PresheafOfModulesOfCommRing R))

@[simps -isSimp]
instance smulOver (U : Cᵒᵖ) (F G : (PresheafOfModulesOfCommRing ((Over.forget U.unop).op ⋙ R))) :
    SMul (R.obj U) (F ⟶ G) where
  smul a φ := {
    app V := ModuleCat.ofHom {
      toFun s := (R.map V.unop.hom.op a) • φ.app _ s
      map_add' := by simp
      map_smul' b s := by
        dsimp at b
        simp [smul_smul, mul_comm b]
    }
    naturality f := by
      ext x
      dsimp
      rw [PresheafOfModules.naturality_apply, G.map_smul]
      congr 1
      change R.map _ a = R.map f.unop.left.op (R.map _ a)
      rw [← comp_apply, ← R.map_comp, ← op_comp, f.unop.w]
  }

lemma over_smul_app_apply
    {U : Cᵒᵖ} {F G : (PresheafOfModulesOfCommRing.{v} ((Over.forget U.unop).op ⋙ R))}
    (a : R.obj U) (φ : F ⟶ G) {V : (Over U.unop)ᵒᵖ} (s : F.obj V) :
    (a • φ).app V s = R.map V.unop.hom.op a • φ.app _ s :=
  rfl

attribute [local simp] smulOver_smul_app

instance (U : Cᵒᵖ) :
    Linear (R.obj U) (PresheafOfModulesOfCommRing.{v} ((Over.forget U.unop).op ⋙ R)) where
  homModule F G :=
    { zero_smul _ := by ext; simp
      one_smul _ := by ext; simp
      mul_smul _ _ _ := by ext; simp [map_mul, mul_smul]
      add_smul _ _ _ := by ext; simp [add_smul]
      smul_zero _ := by ext; simp
      smul_add _ _ _ := by ext; simp}
  smul_comp _ _ _ _ _ _ := by ext; simp
  comp_smul _ _ _ _ _ _ := rfl

variable (F G : PresheafOfModulesOfCommRing.{u} R)

@[simps]
def internalHomMap {U V : C} (f : V ⟶ U) (φ : F.over U ⟶ G.over U) :
    F.over V ⟶ G.over V where
  app W := φ.app ((Over.map f).op.obj W)
  naturality g := φ.naturality ((Over.map f).op.map g)

@[simp]
lemma internalHomMap_smul {U V : Cᵒᵖ} (f : U ⟶ V) (a : R.obj U)
    (φ : F.over U.unop ⟶ G.over U.unop) :
    F.internalHomMap G f.unop (a • φ) = R.map f a • F.internalHomMap G f.unop φ := by
  ext W x
  simp
  rfl

@[simp]
lemma internalHomMap_comp {U V W} (g : W ⟶ V) (f : V ⟶ U) (φ : F.over U ⟶ G.over U) :
    F.internalHomMap G (g ≫ f) φ = F.internalHomMap G g (F.internalHomMap G f φ) := by
  refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
  simp only [internalHomMap_app]
  congr 1
  simp [Over.mapComp_eq]

@[simp]
lemma internalHomMap_id {U : C} (φ : F.over U ⟶ G.over U) :
    F.internalHomMap G (𝟙 U) φ = φ := by
  refine PresheafOfModules.hom_ext (fun _ ↦ ?_)
  simp only [internalHomMap_app]
  congr 1
  simp [Over.mapId_eq]

set_option backward.isDefEq.respectTransparency false in
@[simps]
def internalHom : PresheafOfModulesOfCommRing.{max u u₁ v₁} R where
  obj U := ModuleCat.of (R.obj U) (F.over U.unop ⟶ G.over U.unop)
  map {U V} f := ConcreteCategory.ofHom (C := ModuleCat (R.obj U))
    { toFun := internalHomMap _ _ f.unop
      map_add' _ _ := rfl
      map_smul' a φ := internalHomMap_smul _ _ _ _ _ }
  map_id _ := by ext x; simp [ModuleCat.restrictScalarsId'App_inv_apply (x := x)]
  map_comp {X₁ X₂ X₃} f g := by ext; simp

open Opposite

@[simps]
def internalHomFunctor : PresheafOfModulesOfCommRing.{u} R ⥤
    PresheafOfModulesOfCommRing.{max u u₁ v₁} R where
  obj G := internalHom F G
  map φ :=
    { app V := ModuleCat.ofHom
        { toFun s := s ≫ overHom φ (unop V)
          map_smul' b s := by simp
          map_add' := by simp }
    }

/-- Internal version of the co-Yoneda functor `CategoryTheory.coyoneda` -/
@[simps]
def internalHomCoyoneda :
    (PresheafOfModulesOfCommRing.{u} R)ᵒᵖ ⥤
      PresheafOfModulesOfCommRing.{u} R ⥤
      PresheafOfModulesOfCommRing.{max u u₁ v₁} R where
  obj F := internalHomFunctor (unop F)
  map φ :=
    { app G :=
      { app V := ModuleCat.ofHom
          { toFun s := overHom φ.unop (unop V) ≫ s
            map_add' := by simp
            map_smul' := by simp
          }
      }
    }

end PresheafOfModulesOfCommRing

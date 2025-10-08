/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.AlgebraicGeometry.Modules.Presheaf
import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`, and study its basic functoriality.

-/

universe t u

open CategoryTheory Bicategory

-- to be moved...
namespace TopologicalSpace.Opens

instance {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (F : Opens X ⥤ Opens Y) (G : Opens Y ⥤ Opens Z)
    [Functor.IsContinuous.{t} F (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)]
    [Functor.IsContinuous.{t} G (Opens.grothendieckTopology _) (Opens.grothendieckTopology _)] :
    Functor.IsContinuous.{t} (F ⋙ G) (Opens.grothendieckTopology _)
      (Opens.grothendieckTopology _) :=
  Functor.isContinuous_comp _ _ _ (Opens.grothendieckTopology _) _

end TopologicalSpace.Opens

-- to be moved
namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y : LocallyRingedSpace} (f : X.Hom Y)

abbrev Hom.toSheafHom :
    Y.sheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      _ _ _).obj X.sheaf where
  val := f.c

end AlgebraicGeometry.LocallyRingedSpace

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

variable (X) in
/-- The category of sheaves of modules over a scheme. -/
abbrev Modules := SheafOfModules.{u} X.ringCatSheaf

example : HasSheafify (Opens.grothendieckTopology X) AddCommGrp.{u} :=
  inferInstance

example : Abelian X.Modules := inferInstance

def Hom.toRingCatSheafHom (f : X ⟶ Y) :
    Y.ringCatSheaf ⟶ ((TopologicalSpace.Opens.map f.base).sheafPushforwardContinuous
      _ _ _).obj X.ringCatSheaf :=
  (sheafCompose _ (forget₂ _ RingCat)).map f.toSheafHom

namespace Modules

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

noncomputable def pushforward : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward f.toRingCatSheafHom

noncomputable def pullback : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom

noncomputable def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

variable (X) in
noncomputable def pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

variable (X) in
noncomputable def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

noncomputable def pushforwardComp :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp _ _

noncomputable def pullbackComp :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

@[reassoc]
lemma pseudofunctor_associativity :
    (pullbackComp f (g ≫ h)).inv ≫
      Functor.whiskerRight (pullbackComp g h).inv _ ≫ (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft _ (pullbackComp f g).hom ≫ (pullbackComp (f ≫ g) h).hom =
    eqToHom (by simp) := by
  let e₁ := pullbackComp f (g ≫ h)
  let e₂ := Functor.isoWhiskerRight (pullbackComp g h) (pullback f)
  let e₃ := Functor.isoWhiskerLeft (pullback h) (pullbackComp f g)
  let e₄ := pullbackComp (f ≫ g) h
  change e₁.inv ≫ e₂.inv ≫ (Functor.associator _ _ _).hom ≫ e₃.hom ≫ e₄.hom = _
  have : e₃.hom ≫ e₄.hom = (Functor.associator _ _ _).inv ≫ e₂.hom ≫ e₁.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_assoc.{u}
      h.toRingCatSheafHom g.toRingCatSheafHom f.toRingCatSheafHom)
  simp [this]

@[reassoc]
lemma pseudofunctor_left_unitality :
    (pullbackComp f (𝟙 Y)).inv ≫
      Functor.whiskerRight (pullbackId Y).hom (pullback f) ≫ (Functor.leftUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp f (𝟙 _)
  let e₂ := Functor.isoWhiskerRight (pullbackId Y) (pullback f)
  let e₃ := (pullback f).leftUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_id_comp.{u} f.toRingCatSheafHom)
  simp [← this]

@[reassoc]
lemma pseudofunctor_right_unitality :
    (pullbackComp (𝟙 X) f).inv ≫
      Functor.whiskerLeft (pullback f) (pullbackId X).hom ≫ (Functor.rightUnitor _).hom =
        eqToHom (by simp) := by
  let e₁ := pullbackComp (𝟙 _) f
  let e₂ := Functor.isoWhiskerLeft (pullback f) (pullbackId _)
  let e₃ := (pullback f).rightUnitor
  change e₁.inv ≫ e₂.hom ≫ e₃.hom = _
  have : e₁.hom = e₂.hom ≫ e₃.hom :=
    congr_arg Iso.hom (SheafOfModules.pullback_comp_id.{u} f.toRingCatSheafHom)
  simp [← this]

noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat) :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Adj.mk (Cat.of X.unop.Modules))
    (fun {Y X} f ↦ .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun X ↦ Adj.iso₂Mk (pullbackId _) (pushforwardId _).symm (by
      dsimp
      sorry))
    (fun {Z Y X} f g ↦ Adj.iso₂Mk (pullbackComp _ _).symm (pushforwardComp _ _) (by
      dsimp
      sorry))
    (fun _ _ _ ↦ by ext : 1; apply pseudofunctor_associativity _ _ _)
    (fun _ ↦ by ext : 1; apply pseudofunctor_left_unitality)
    (fun _ ↦ by ext : 1; apply pseudofunctor_right_unitality)

set_option maxHeartbeats 400000 in -- this is slow
attribute [simps! obj_obj map_l map_r map_adj mapId_hom_τl mapId_hom_τr mapId_inv_τl mapId_inv_τr
  mapComp_hom_τl mapComp_hom_τr mapComp_inv_τl mapComp_inv_τr] pseudofunctor

end Modules

end AlgebraicGeometry.Scheme

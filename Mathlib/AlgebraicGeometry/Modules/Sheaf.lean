/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Andrew Yang
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The category of sheaves of modules over a scheme

In this file, we define the abelian category of sheaves of modules
`X.Modules` over a scheme `X`, and study its basic functoriality.

-/

@[expose] public section

universe t u

open CategoryTheory Bicategory

namespace AlgebraicGeometry.Scheme

variable {X Y Z T : Scheme.{u}}

variable (X) in
/-- The category of sheaves of modules over a scheme. -/
def Modules := SheafOfModules.{u} X.ringCatSheaf

namespace Modules

/-- Morphisms between `𝒪ₓ`-modules. -/
def Hom (M N : X.Modules) : Type u := SheafOfModules.Hom M N

instance : Category X.Modules where
  Hom := Modules.Hom
  __ := inferInstanceAs (Category (SheafOfModules.{u} X.ringCatSheaf))

instance : Preadditive X.Modules :=
  inferInstanceAs (Preadditive (SheafOfModules.{u} X.ringCatSheaf))

instance : Abelian X.Modules :=
  inferInstanceAs (Abelian (SheafOfModules.{u} X.ringCatSheaf))

variable (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ T)

/-- The pushforward functor for categories of sheaves of modules over schemes. -/
noncomputable def pushforward : X.Modules ⥤ Y.Modules :=
  SheafOfModules.pushforward f.toRingCatSheafHom

/-- The pullback functor for categories of sheaves of modules over schemes. -/
noncomputable def pullback : Y.Modules ⥤ X.Modules :=
  SheafOfModules.pullback f.toRingCatSheafHom

/-- The pullback functor for categories of sheaves of modules over schemes
is left adjoint to the pushforward functor. -/
noncomputable def pullbackPushforwardAdjunction : pullback f ⊣ pushforward f :=
  SheafOfModules.pullbackPushforwardAdjunction _

variable (X) in
/-- The pushforward of sheaves of modules by the identity morphism identifies
to the identity functor. -/
noncomputable def pushforwardId : pushforward (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pushforwardId _

variable (X) in
/-- The pullback of sheaves of modules by the identity morphism identifies
to the identity functor. -/
noncomputable def pullbackId : pullback (𝟙 X) ≅ 𝟭 _ :=
  SheafOfModules.pullbackId _

variable (X) in
lemma conjugateEquiv_pullbackId_hom :
    conjugateEquiv .id (pullbackPushforwardAdjunction (𝟙 X)) (pullbackId X).hom =
      (pushforwardId X).inv :=
  SheafOfModules.conjugateEquiv_pullbackId_hom _

/-- The composition of two pushforward functors for sheaves of modules on schemes
identify to the pushforward for the composition. -/
noncomputable def pushforwardComp :
    pushforward f ⋙ pushforward g ≅ pushforward (f ≫ g) :=
  SheafOfModules.pushforwardComp _ _

/-- The composition of two pullback functors for sheaves of modules on schemes
identify to the pullback for the composition. -/
noncomputable def pullbackComp :
    pullback g ⋙ pullback f ≅ pullback (f ≫ g) :=
  SheafOfModules.pullbackComp _ _

lemma conjugateEquiv_pullbackComp_inv :
    conjugateEquiv ((pullbackPushforwardAdjunction g).comp (pullbackPushforwardAdjunction f))
      (pullbackPushforwardAdjunction (f ≫ g)) (pullbackComp f g).inv =
    (pushforwardComp f g).hom :=
  SheafOfModules.conjugateEquiv_pullbackComp_inv _ _

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

attribute [local simp] pseudofunctor_associativity pseudofunctor_left_unitality
  pseudofunctor_right_unitality Bicategory.toNatTrans_conjugateEquiv
  conjugateEquiv_pullbackId_hom Adjunction.ofCat_comp conjugateEquiv_pullbackComp_inv in
/-- The pseudofunctor from `Schemeᵒᵖ` to the bicategory of adjunctions which sends
a scheme `X` to the category `X.Modules` of sheaves of modules over `X`.
(This contains both the covariant and the contravariant functorialities of
these categories.) -/
@[simps! obj_obj map_l map_r map_adj
  mapId_hom_τl mapId_hom_τr mapId_inv_τl mapId_inv_τr
  mapComp_hom_τl mapComp_hom_τr mapComp_inv_τl mapComp_inv_τr]
noncomputable def pseudofunctor :
    Pseudofunctor (LocallyDiscrete Scheme.{u}ᵒᵖ) (Adj Cat) :=
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Adj.mk (Cat.of X.unop.Modules))
    (fun f ↦ .mk (pullbackPushforwardAdjunction f.unop).toCat)
    (fun _ ↦ Adj.iso₂Mk (Cat.Hom.isoMk (pullbackId _))
        (Cat.Hom.isoMk (pushforwardId _).symm))
    (fun _ _ ↦ Adj.iso₂Mk (Cat.Hom.isoMk (pullbackComp _ _).symm)
        (Cat.Hom.isoMk (pushforwardComp _ _)))

end Modules

end AlgebraicGeometry.Scheme

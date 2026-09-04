/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Sites.Point.Basic

/-!
# Modules over presheaves and sheaves of commutative rings

This file provides short names for categories and functors obtained from a presheaf or
sheaf of commutative rings by forgetting to rings. In particular, these names avoid
repeatedly writing the relevant forgetful functor or `sheafCompose`.
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor Limits

/-! ## Categories -/

/-- The category of presheaves of modules over a presheaf of commutative rings. -/
abbrev PresheafOfModulesOfCommRing {C : Type u₁} [Category.{v₁} C]
    (R : Cᵒᵖ ⥤ CommRingCat.{u}) :=
  PresheafOfModules.{v} (R ⋙ forget₂ _ _)

/-- The category of sheaves of modules over a sheaf of commutative rings. -/
abbrev SheafOfModulesOfCommRing {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat RingCat)] :=
  SheafOfModules.{v} ((sheafCompose J (forget₂ _ _)).obj R)

/-! ## Presheaves of modules -/

namespace PresheafOfModulesOfCommRing

section Basic

variable {C : Type u₁} [Category.{v₁} C]
  {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Construct a presheaf of modules over a presheaf of commutative rings. -/
abbrev mk (obj : ∀ (X : Cᵒᵖ), ModuleCat.{v} (R.obj X)) (map : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (obj Y))
    (map_id : ∀ (X : Cᵒᵖ), map (𝟙 X) = (ModuleCat.restrictScalarsId' (R.map (𝟙 X)).hom
      (congrArg CommRingCat.Hom.hom (R.map_id X))).inv.app _)
    (map_comp : ∀ {X Y Z : Cᵒᵖ} (f : X ⟶ Y) (g : Y ⟶ Z),
      map (f ≫ g) = map f ≫ (ModuleCat.restrictScalars _).map (map g) ≫
        (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
          (congrArg CommRingCat.Hom.hom <| R.map_comp f g)).inv.app _) :
    PresheafOfModulesOfCommRing.{v} R where
  obj := obj
  map := map
  map_id := map_id
  map_comp := map_comp

/-- Evaluate a presheaf of modules over a presheaf of commutative rings at an object. -/
abbrev obj (F : PresheafOfModulesOfCommRing.{v} R) (X : Cᵒᵖ) : ModuleCat.{v} (R.obj X) :=
  PresheafOfModules.obj F X

/-- The restriction map of a presheaf of modules over a presheaf of commutative rings. -/
abbrev map (F : PresheafOfModulesOfCommRing.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    F.obj X ⟶ (ModuleCat.restrictScalars (R.map f).hom).obj (F.obj Y) :=
  PresheafOfModules.map _ _

/-- Construct a morphism of presheaves of modules over a presheaf of commutative rings. -/
abbrev mkHom {M₁ M₂ : PresheafOfModulesOfCommRing.{v} R}
    (app : ∀ (X : Cᵒᵖ), M₁.obj X ⟶ M₂.obj X)
    (naturality : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y) =
        app X ≫ M₂.map f) : M₁ ⟶ M₂ where
  app := app
  naturality := naturality

/-- A morphism of presheaves of modules over commutative rings commutes with restriction. -/
lemma naturality_apply {M₁ M₂ : PresheafOfModulesOfCommRing.{v} R} (φ : M₁ ⟶ M₂)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : M₁.obj X) :
    φ.app Y (M₁.map f x) = M₂.map f (φ.app X x) :=
  PresheafOfModules.naturality_apply φ f x

/-- Construct an isomorphism of presheaves of modules over a presheaf of commutative rings. -/
abbrev isoMk {M₁ M₂ : PresheafOfModulesOfCommRing.{v} R}
    (app : ∀ (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (app Y).hom =
        (app X).hom ≫ M₂.map f := by cat_disch) : M₁ ≅ M₂ :=
  PresheafOfModules.isoMk app naturality

/-- The free presheaf of modules of rank one over a presheaf of commutative rings. -/
noncomputable abbrev unit (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModules.unit (R ⋙ forget₂ _ _)

end Basic

section ChangeOfRings

variable {C : Type u₁} [Category.{v₁} C]
  {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S)

/-- Restriction of scalars along a morphism of presheaves of commutative rings. -/
noncomputable abbrev restrictScalars :
    PresheafOfModulesOfCommRing.{v} S ⥤ PresheafOfModulesOfCommRing.{v} R :=
  PresheafOfModules.restrictScalars (whiskerRight φ (forget₂ _ _))

end ChangeOfRings

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- The pushforward functor along `F` for modules over a presheaf of commutative rings. -/
abbrev pushforward₀ (F : C ⥤ D) (R : Dᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{v} R ⥤
      PresheafOfModulesOfCommRing.{v} (F.op ⋙ R) :=
  PresheafOfModules.pushforward₀ F (R ⋙ forget₂ _ _)

variable {F : C ⥤ D} {R : Dᵒᵖ ⥤ CommRingCat.{u}}
  {S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : S ⟶ F.op ⋙ R)

/-- The pushforward functor induced by a morphism of presheaves of commutative rings. -/
noncomputable abbrev pushforward :
    PresheafOfModulesOfCommRing.{v} R ⥤ PresheafOfModulesOfCommRing.{v} S :=
  PresheafOfModules.pushforward (whiskerRight φ (forget₂ _ _))

/-- The pullback functor induced by a morphism of presheaves of commutative rings. -/
noncomputable abbrev pullback [(pushforward.{v} φ).IsRightAdjoint] :
    PresheafOfModulesOfCommRing.{v} S ⥤ PresheafOfModulesOfCommRing.{v} R :=
  PresheafOfModules.pullback (whiskerRight φ (forget₂ _ _))

/-- The adjunction between pullback and pushforward for modules over presheaves of
commutative rings. -/
noncomputable abbrev pullbackPushforwardAdjunction
    [(pushforward.{v} φ).IsRightAdjoint] :
    pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

end Pushforward

section Colimit

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- The constant-presheaf functor associated to a cocone of commutative rings. -/
noncomputable abbrev constFunctor (cR : Cocone R) :
    ModuleCat.{u} cR.pt ⥤ PresheafOfModulesOfCommRing.{u} R :=
  PresheafOfModules.constFunctor ((forget₂ _ _).mapCocone cR)

variable [LocallySmall.{u} C] [IsCofiltered C] [InitiallySmall.{u} C]
  {cR : Cocone R} (hcR : IsColimit cR)

/-- The colimit-module functor associated to a colimit cocone of commutative rings. -/
noncomputable abbrev colimitFunctor :
    PresheafOfModulesOfCommRing.{u} R ⥤ ModuleCat.{u} cR.pt :=
  PresheafOfModules.colimitFunctor
    (isColimitOfPreserves (forget₂ _ _) hcR)

/-- The adjunction between the colimit-module and constant-presheaf functors. -/
noncomputable abbrev colimitAdjunction :
    colimitFunctor hcR ⊣ constFunctor cR :=
  PresheafOfModules.colimitAdjunction
    (isColimitOfPreserves (forget₂ _ _) hcR)

/-- The coprojection `P.obj U →+ (colimitFunctor hcR).obj P` into the colimit module. -/
noncomputable def ιColimitFunctor
    (P : PresheafOfModulesOfCommRing.{u} R) (U : Cᵒᵖ) :
    P.obj U →+ (colimitFunctor hcR).obj P :=
  (colimit.ι P.presheaf U).hom

/-- The coprojections into the colimit module commute with restriction maps. -/
@[simp]
lemma ιColimitFunctor_map
    (P : PresheafOfModulesOfCommRing.{u} R) {V U : Cᵒᵖ}
    (f : V ⟶ U) (x : P.obj V) :
    ιColimitFunctor hcR P U (P.map f x) = ιColimitFunctor hcR P V x :=
  ConcreteCategory.congr_hom (colimit.w P.presheaf f) x

/-- The colimit cocone on the underlying presheaf of additive commutative groups. -/
noncomputable def coconeColimitFunctor
    (P : PresheafOfModulesOfCommRing.{u} R) : Cocone P.presheaf where
  pt := (forget₂ _ AddCommGrpCat).obj ((colimitFunctor hcR).obj P)
  ι.app U := AddCommGrpCat.ofHom (ιColimitFunctor hcR P U)
  ι.naturality V U f := by
    ext x
    exact ιColimitFunctor_map hcR P f x

/-- The cocone `coconeColimitFunctor hcR P` is a colimit cocone. -/
noncomputable def isColimitCoconeColimitFunctor
    (P : PresheafOfModulesOfCommRing.{u} R) :
    IsColimit (coconeColimitFunctor hcR P) :=
  colimit.isColimit P.presheaf

end Colimit

section Fiber

attribute [local instance] hasColimitsOfShape_of_finallySmall
  IsFiltered.isSifted FinallySmall.preservesColimitsOfShape_of_isFiltered

variable {C : Type u₁} [Category.{v₁} C] [LocallySmall.{u} C]
  {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{u} J)

/-- The fiber functor at a point for modules over a presheaf of commutative rings. -/
noncomputable def fiber (R : Cᵒᵖ ⥤ CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{u} R ⥤
      ModuleCat.{u} (Φ.presheafFiber.obj R :) :=
  pushforward₀ (CategoryOfElements.π Φ.fiber) R ⋙
    colimitFunctor
      (colimit.isColimit ((CategoryOfElements.π Φ.fiber).op ⋙ R))

end Fiber

end PresheafOfModulesOfCommRing

/-! ## Sheaves of modules -/

namespace SheafOfModulesOfCommRing

section Basic

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The underlying presheaf of modules of a sheaf of modules. -/
abbrev val {R : Sheaf J CommRingCat.{u}} (F : SheafOfModulesOfCommRing.{v} R) :
    PresheafOfModulesOfCommRing.{v} R.obj :=
  SheafOfModules.val F

/-- The functor forgetting the sheaf condition on a sheaf of modules. -/
abbrev forget (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{v} R ⥤ PresheafOfModulesOfCommRing.{v} R.obj :=
  SheafOfModules.forget _

/-- The forgetful functor from sheaves of modules to presheaves of modules is fully
faithful. -/
abbrev fullyFaithfulForget (R : Sheaf J CommRingCat.{u}) :
    (forget.{v} R).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

/-- The functor forgetting the sheaf condition is faithful. -/
instance (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).Faithful :=
  (fullyFaithfulForget R).faithful

/-- The functor forgetting the sheaf condition is full. -/
instance (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).Full :=
  (fullyFaithfulForget R).full

/-- The functor forgetting the sheaf condition reflects isomorphisms. -/
instance (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).ReflectsIsomorphisms :=
  (fullyFaithfulForget R).reflectsIsomorphisms

end Basic

section ChangeOfRings

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R S : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Restriction of scalars along a morphism of sheaves of commutative rings. -/
noncomputable abbrev restrictScalars (φ : R ⟶ S) :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ _ _)).map φ)

end ChangeOfRings

section Pushforward

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J CommRingCat.{u}} {R : Sheaf K CommRingCat.{u}}
  [Functor.IsContinuous F J K]
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [K.HasSheafCompose (forget₂ CommRingCat RingCat)]
  (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat.{u} J K).obj R)

/-- The pushforward functor induced by a morphism of sheaves of commutative rings. -/
noncomputable abbrev pushforward :
    SheafOfModulesOfCommRing.{v} R ⥤ SheafOfModulesOfCommRing.{v} S :=
  SheafOfModules.pushforward
    ((sheafCompose J (forget₂ _ _)).map φ)

/-- The pullback functor induced by a morphism of sheaves of commutative rings. -/
noncomputable abbrev pullback [(pushforward.{v} φ).IsRightAdjoint] :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.pullback
    ((sheafCompose J (forget₂ _ _)).map φ)

/-- The adjunction between pullback and pushforward for modules over sheaves of
commutative rings. -/
noncomputable abbrev pullbackPushforwardAdjunction
    [(pushforward.{v} φ).IsRightAdjoint] :
    pullback.{v} φ ⊣ pushforward.{v} φ :=
  Adjunction.ofIsRightAdjoint (pushforward φ)

/-- Pushforward of sheaves of modules commutes with forgetting the sheaf condition. -/
noncomputable def pushforwardCompForgetIso :
    pushforward.{v} φ ⋙ forget S ≅
      forget R ⋙ PresheafOfModulesOfCommRing.pushforward.{v}
        ((sheafToPresheaf J CommRingCat).map φ) :=
  Iso.refl _

end Pushforward

section Over

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- Restriction of sheaves of modules to the over category of an object. -/
noncomputable abbrev overFunctor (X : C) :
    SheafOfModulesOfCommRing.{v} R ⥤ SheafOfModulesOfCommRing.{v} (R.over X) :=
  SheafOfModules.overFunctor _ X

/-- Pushforward of sheaves of modules along the functor `Over.map f`. -/
noncomputable abbrev overPullback {X Y : C} (f : X ⟶ Y) :
    SheafOfModulesOfCommRing.{v} (R.over Y) ⥤
      SheafOfModulesOfCommRing.{v} (R.over X) :=
  SheafOfModules.pushforward (F := Over.map f) (𝟙 _)

/-- Restriction to an over category is compatible with `overPullback`. -/
noncomputable abbrev overFunctorCompOverPullback {X Y : C} (f : X ⟶ Y) :
    overFunctor.{v} R Y ⋙ overPullback.{v} R f ≅ overFunctor.{v} R X :=
  SheafOfModules.pushforwardComp _ _

end Over

section Fiber

variable {C : Type u₁} [Category.{v₁} C] [LocallySmall.{u} C]
  {J : GrothendieckTopology C} (Φ : GrothendieckTopology.Point.{u} J)
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]

/-- The fiber functor at a point for modules over a sheaf of commutative rings. -/
noncomputable def fiber (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{u} R ⥤ ModuleCat.{u} (Φ.presheafFiber.obj R.obj :) :=
  forget R ⋙ PresheafOfModulesOfCommRing.fiber Φ R.obj

end Fiber

end SheafOfModulesOfCommRing

/-! ## Sheafification -/

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat)]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [HasWeakSheafify J AddCommGrpCat.{v}]

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification functor for modules over a sheaf of commutative rings. -/
noncomputable abbrev sheafification (R : Sheaf J CommRingCat.{u}) :
    PresheafOfModulesOfCommRing.{v} R.obj ⥤ SheafOfModulesOfCommRing.{v} R :=
  PresheafOfModules.sheafification.{v} (J := J)
    (R₀ := R.obj ⋙ forget₂ _ _)
    (R := (sheafCompose J (forget₂ _ _)).obj R) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between sheafification and the functor forgetting the sheaf condition. -/
noncomputable abbrev sheafificationAdjunction (R : Sheaf J CommRingCat.{u}) :
    sheafification.{v} R ⊣ SheafOfModulesOfCommRing.forget.{v} R :=
  PresheafOfModules.sheafificationAdjunction (𝟙 _)

end PresheafOfModulesOfCommRing

/-
Copyright (c) 2026 Brian Nugent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Brian Nugent
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.Algebra.Category.Ring.Limits

/-!
# Modules over sheaves of commutative rings

This file provides short names for categories and functors obtained from a sheaf of commutative
rings by forgetting to rings. In particular, these names reduce the need for
repeatedly writing the relevant forgetful functor
-/

@[expose] public section

universe v v₁ v₂ u₁ u₂ u

open CategoryTheory Functor

/-- The category of sheaves of modules over a sheaf of commutative rings. -/
abbrev SheafOfModulesOfCommRing {C : Type u₁} [Category.{v₁} C]
    {J : GrothendieckTopology C} (R : Sheaf J CommRingCat.{u})
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] :=
  SheafOfModules.{v} ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)

namespace SheafOfModulesOfCommRing

section Basic

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J CommRingCat.{u}}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The underlying presheaf of modules over commutative rings. -/
abbrev val (F : SheafOfModulesOfCommRing.{v} R) : PresheafOfModulesOfCommRing.{v} R.obj :=
  SheafOfModules.val F

/-- Construct a sheaf of modules over a sheaf of commutative rings. -/
abbrev mk (val : PresheafOfModulesOfCommRing.{v} R.obj)
    (isSheaf : Presheaf.IsSheaf J val.presheaf) : SheafOfModulesOfCommRing.{v} R where
  val := val
  isSheaf := isSheaf

/-- Evaluate a sheaf of modules over a sheaf of commutative rings at an object. -/
abbrev obj (F : SheafOfModulesOfCommRing.{v} R) (X : Cᵒᵖ) : ModuleCat.{v} (R.obj.obj X) :=
  F.val.obj X

/-- The restriction map of a sheaf of modules over a sheaf of commutative rings. -/
abbrev map (F : SheafOfModulesOfCommRing.{v} R) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    F.obj X ⟶ (ModuleCat.restrictScalars (R.obj.map f).hom).obj (F.obj Y) :=
  F.val.map f

/-- Construct a morphism of sheaves of modules over a sheaf of commutative rings. -/
abbrev homMk {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (app : ∀ (X : Cᵒᵖ), M₁.obj X ⟶ M₂.obj X)
    (naturality : ∀ {X Y : Cᵒᵖ} (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.obj.map f).hom).map (app Y) =
        app X ≫ M₂.map f := by cat_disch) : M₁ ⟶ M₂ where
  val := PresheafOfModulesOfCommRing.homMk app naturality

/-- Construct an isomorphism of sheaves of modules over a sheaf of commutative rings. -/
abbrev isoMk {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (app : ∀ (X : Cᵒᵖ), M₁.obj X ≅ M₂.obj X)
    (naturality : ∀ ⦃X Y : Cᵒᵖ⦄ (f : X ⟶ Y),
      M₁.map f ≫ (ModuleCat.restrictScalars (R.obj.map f).hom).map (app Y).hom =
        (app X).hom ≫ M₂.map f := by cat_disch) : M₁ ≅ M₂ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModulesOfCommRing.isoMk app naturality)

/-- The family of linear maps associated to a morphism of sheaves of modules. -/
abbrev _root_.SheafOfModules.Hom.app' {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (f : M₁ ⟶ M₂) (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X := f.val.app X

/-- The forgetful functor from sheaves to presheaves of modules over commutative rings. -/
abbrev forget (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{v} R ⥤ PresheafOfModulesOfCommRing.{v} R.obj :=
  SheafOfModules.forget _

abbrev fullyFaithfulForget (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

instance (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).Full := (fullyFaithfulForget R).full

instance (R : Sheaf J CommRingCat.{u}) : (forget.{v} R).Faithful := (fullyFaithfulForget R).faithful

/-- The free sheaf of modules of rank one over a sheaf of commutative rings. -/
noncomputable abbrev unit (R : Sheaf J CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{u} R :=
  SheafOfModules.unit _

/-- Restriction of scalars along a morphism of sheaves of commutative rings. -/
noncomputable abbrev restrictScalars {S : Sheaf J CommRingCat.{u}} (φ : R ⟶ S) :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.restrictScalars ((sheafCompose J (forget₂ _ _)).map φ)

lemma naturality_apply {M₁ M₂ : SheafOfModulesOfCommRing.{v} R}
    (f : M₁ ⟶ M₂) {X Y : Cᵒᵖ} (g : X ⟶ Y) (x : M₁.obj X) :
    (f.app' Y) ((M₁.map g) x) = (M₂.map g) ((f.app' X) x) :=
  PresheafOfModulesOfCommRing.naturality_apply f.val g x

end Basic

section PushforwardPullback

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [K.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The pushforward functor along a continuous functor for modules over a sheaf of
commutative rings. -/
noncomputable abbrev pushforward₀ (F : C ⥤ D) [F.IsContinuous J K]
    (R : Sheaf K CommRingCat.{u}) :
    SheafOfModulesOfCommRing.{v} R ⥤
      SheafOfModulesOfCommRing.{v} ((F.sheafPushforwardContinuous CommRingCat J K).obj R) :=
  SheafOfModules.pushforward (F := F) (𝟙 _)

variable {F : C ⥤ D} [F.IsContinuous J K] {R : Sheaf K CommRingCat.{u}}
  {S : Sheaf J CommRingCat.{u}} (φ : S ⟶ (F.sheafPushforwardContinuous CommRingCat J K).obj R)

/-- The pushforward functor induced by a morphism of sheaves of commutative rings. -/
noncomputable abbrev pushforward :
    SheafOfModulesOfCommRing.{v} R ⥤ SheafOfModulesOfCommRing.{v} S :=
  SheafOfModules.pushforward (F := F)
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

/-- The pullback functor induced by a morphism of sheaves of commutative rings. -/
noncomputable abbrev pullback [(pushforward.{v} φ).IsRightAdjoint] :
    SheafOfModulesOfCommRing.{v} S ⥤ SheafOfModulesOfCommRing.{v} R :=
  SheafOfModules.pullback (F := F)
    ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map φ)

/-- The adjunction between pullback and pushforward for modules over sheaves of
commutative rings. -/
noncomputable abbrev pullbackPushforwardAdjunction
    [(pushforward.{v} φ).IsRightAdjoint] :
    pullback.{v} φ ⊣ pushforward.{v} φ :=
  SheafOfModules.pullbackPushforwardAdjunction _

end PushforwardPullback

end SheafOfModulesOfCommRing

namespace PresheafOfModulesOfCommRing

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasWeakSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

set_option backward.isDefEq.respectTransparency false in
/-- The sheafification functor for modules over a sheaf of commutative rings. -/
noncomputable abbrev sheafification :
    PresheafOfModulesOfCommRing.{v} R.obj ⥤ SheafOfModulesOfCommRing.{v} R :=
  PresheafOfModules.sheafification (R := (sheafCompose J (forget₂ _ _)).obj R) (𝟙 _)

set_option backward.isDefEq.respectTransparency false in
/-- The adjunction between sheafification and the forgetful functor for modules over a sheaf of
commutative rings. -/
noncomputable abbrev sheafificationAdjunction :
    sheafification.{v} R ⊣ SheafOfModulesOfCommRing.forget R :=
  PresheafOfModules.sheafificationAdjunction (𝟙 _)

end PresheafOfModulesOfCommRing

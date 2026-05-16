/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Sites.Point.Conservative
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctorMonoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Point
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization

/-!
# Monoidal structure on sheaves of modules

-/

@[expose] public section

universe w v u

open CategoryTheory MonoidalCategory BraidedCategory Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

namespace CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

section

variable {P : ObjectProperty (GrothendieckTopology.Point.{w} J)} [LocallySmall.{w} C]
  (hP : P.IsConservativeFamilyOfPoints)
  (R₀ : Cᵒᵖ ⥤ CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]

include hP

lemma presheafOfModulesW_iff {F G : PresheafOfModules.{w} (R₀ ⋙ forget₂ _ _)} (f : F ⟶ G) :
    J.W ((PresheafOfModules.toPresheaf _).map f) ↔
      ∀ (Φ : P.FullSubcategory), IsIso ((Φ.obj.presheafOfModulesFiber _).map f) := by
  rw [hP.W_iff]
  refine forall_congr' (fun Φ ↦ ?_)
  simp only [← isIso_iff_of_reflects_iso _
    (forget₂ (ModuleCat.{w} (Φ.obj.presheafFiber.obj R₀ :)) AddCommGrpCat)]
  rfl

lemma isMonoidal_presheafOfModulesW :
    (J.W.inverseImage (PresheafOfModules.toPresheaf (R₀ ⋙ forget₂ _ _))).IsMonoidal :=
  .mk' _ (fun f g hf hg ↦ by
    simp only [MorphismProperty.inverseImage_iff, hP.presheafOfModulesW_iff] at hf hg ⊢
    intro Φ
    rw [Functor.Monoidal.map_tensor]
    infer_instance)

end

instance (R₀ : Cᵒᵖ ⥤ CommRingCat.{w}) [HasWeakSheafify J AddCommGrpCat.{w}]
    [GrothendieckTopology.HasEnoughPoints.{w} J] [LocallySmall.{w} C] :
    (J.W.inverseImage (PresheafOfModules.toPresheaf (R₀ ⋙ forget₂ _ _))).IsMonoidal := by
  obtain ⟨P, _, hP⟩ := GrothendieckTopology.HasEnoughPoints.exists_objectProperty J
  exact hP.isMonoidal_presheafOfModulesW _

end CategoryTheory.ObjectProperty.IsConservativeFamilyOfPoints

namespace SheafOfModules

variable [HasWeakSheafify J AddCommGrpCat.{w}] (R : Sheaf J CommRingCat.{w})

abbrev W : MorphismProperty (PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _)) :=
  J.W.inverseImage (PresheafOfModules.toPresheaf _)

example [LocallySmall.{w} C] [GrothendieckTopology.HasEnoughPoints.{w} J] :
    (W R).IsMonoidal := inferInstance

variable [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat)]
  [J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat)]
  [(W R).IsMonoidal]

-- to be moved
abbrev forgetOfCommRing :
    SheafOfModules.{w} ((sheafCompose J (forget₂ _ _)).obj R) ⥤
    PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _) :=
  SheafOfModules.forget _

abbrev fullyFaithfulForgetOfCommRing : (forgetOfCommRing.{w} R).FullyFaithful :=
  SheafOfModules.fullyFaithfulForget _

instance : (forgetOfCommRing.{w} R).Faithful :=
  (fullyFaithfulForgetOfCommRing R).faithful

instance : (forgetOfCommRing.{w} R).Full :=
  (fullyFaithfulForgetOfCommRing R).full

-- to be moved
set_option backward.isDefEq.respectTransparency false in
noncomputable abbrev _root_.PresheafOfModules.sheafificationOfCommRing :
    PresheafOfModules.{w} (R.obj ⋙ forget₂ _ _) ⥤
      SheafOfModules.{w} ((sheafCompose J (forget₂ _ _)).obj R) :=
  (PresheafOfModules.sheafification.{w} (J := J) (R₀ := R.obj ⋙ forget₂ _ _)
      (R := ((sheafCompose J (forget₂ _ _)).obj R)) (𝟙 _))

-- to be moved
set_option backward.isDefEq.respectTransparency false in
noncomputable abbrev _root_.PresheafOfModules.sheafificationAdjunctionOfCommRing :
    PresheafOfModules.sheafificationOfCommRing.{w} R ⊣ forgetOfCommRing.{w} R :=
  PresheafOfModules.sheafificationAdjunction (𝟙 _)

instance : (PresheafOfModules.sheafificationOfCommRing.{w} R).IsLeftAdjoint :=
  (PresheafOfModules.sheafificationAdjunctionOfCommRing R).isLeftAdjoint

instance : (PresheafOfModules.sheafificationOfCommRing R).IsLocalization (W R) := by
  dsimp [PresheafOfModules.sheafificationOfCommRing]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
noncomputable instance monoidalCategory :
    MonoidalCategory (SheafOfModules.{w} ((sheafCompose J (forget₂ _ _)).obj R)) :=
  inferInstanceAs (MonoidalCategory (LocalizedMonoidal
    (PresheafOfModules.sheafificationOfCommRing R) (W R) (unit := unit _)
    (asIso ((PresheafOfModules.sheafificationAdjunctionOfCommRing.{w} R).counit.app (unit _)))))

set_option backward.isDefEq.respectTransparency false in
noncomputable instance symmetricCategory :
    SymmetricCategory (SheafOfModules.{w} ((sheafCompose J (forget₂ _ _)).obj R)) :=
  inferInstanceAs (SymmetricCategory (LocalizedMonoidal
    (PresheafOfModules.sheafificationOfCommRing R) (W R) (unit := unit _)
    (asIso ((PresheafOfModules.sheafificationAdjunctionOfCommRing.{w} R).counit.app (unit _)))))

set_option backward.isDefEq.respectTransparency false in
noncomputable instance : (PresheafOfModules.sheafificationOfCommRing.{w} R).Monoidal :=
  inferInstanceAs (Localization.Monoidal.toMonoidalCategory
    (PresheafOfModules.sheafificationOfCommRing R) _ _).Monoidal

noncomputable instance : (forgetOfCommRing.{w} R).LaxMonoidal :=
  (PresheafOfModules.sheafificationAdjunctionOfCommRing R).rightAdjointLaxMonoidal

example : (PresheafOfModules.sheafificationAdjunctionOfCommRing R).IsMonoidal := by
  infer_instance

section

variable (F : (SheafOfModules.{w} ((sheafCompose J (forget₂ _ _)).obj R)))

set_option backward.isDefEq.respectTransparency false in
instance : PreservesColimitsOfSize.{w, w} (tensorLeft F) := by
  let adj := PresheafOfModules.sheafificationAdjunctionOfCommRing.{w} R
  rw [adj.preservesColimitsOfSize_iff]
  apply preservesColimits_of_natIso
    ((Functor.Monoidal.commTensorLeft (PresheafOfModules.sheafificationOfCommRing R) _).symm ≪≫
    Functor.isoWhiskerLeft _ ((curriedTensor _).mapIso
      (asIso (adj.counit.app F))))

instance : PreservesColimitsOfSize.{w, w} (tensorRight F) :=
  preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight F)

instance : PreservesFiniteColimits (tensorLeft F) :=
  PreservesColimitsOfSize.preservesFiniteColimits (tensorLeft F)

instance : PreservesFiniteColimits (tensorRight F) :=
  PreservesColimitsOfSize.preservesFiniteColimits (tensorRight F)

instance : (tensorLeft F).Additive :=
  Functor.additive_of_preserves_binary_coproducts _

instance : (tensorRight F).Additive :=
  Functor.additive_of_preserves_binary_coproducts _

end

instance : MonoidalPreadditive (SheafOfModules.{w} ((sheafCompose J (forget₂ _ _)).obj R)) :=
  .of_functorAdditive _

end SheafOfModules

/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Functor.KanExtension.DenseIff
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.CategoryTheory.Presentable.Continuous
public import Mathlib.CategoryTheory.Presentable.Dense

/-!
# The representation theorem

In this file, we show that if `C` is a locally `κ`-presentable category,
then `C` identifies to the category of `κ`-continuous presheaves on
the full subcategory of `κ`-presentable objects of `C`.

-/

@[expose] public section

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace IsCardinalLocallyPresentable

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable C κ]

instance (X : C) :
    Functor.IsCardinalContinuous
      ((Presheaf.restrictedShrinkYoneda (isCardinalPresentable C κ).ι).obj X) κ where
  preservesLimitsOfShape J _ _ := by
    have : (isCardinalPresentable C κ).IsClosedUnderColimitsOfShape Jᵒᵖ :=
      isClosedUnderColimitsOfShape_isCardinalPresentable _ (by simpa)
    have : PreservesLimitsOfShape J (isCardinalPresentable C κ).ι.op :=
      preservesLimitsOfShape_op _ _
    dsimp [Presheaf.restrictedShrinkYoneda]
    infer_instance

open CategoryTheory.Functor in
@[implicit_reducible]
noncomputable def toCardinalContinuous :
    C ⥤ (Functor.isCardinalContinuous
      (isCardinalPresentable C κ).FullSubcategoryᵒᵖ (Type w) κ).FullSubcategory :=
  ObjectProperty.lift _ (Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _))
    inferInstance

noncomputable def toCardinalContinuousCompIso :
    toCardinalContinuous C κ ⋙ ObjectProperty.ι _ ≅
      Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _) := Iso.refl _

instance : (toCardinalContinuous C κ).Faithful := by
  have := Functor.Faithful.of_iso (toCardinalContinuousCompIso C κ).symm
  exact Functor.Faithful.of_comp _ (ObjectProperty.ι _)

instance : (toCardinalContinuous C κ).Full := by
  have := Functor.Full.of_iso (toCardinalContinuousCompIso C κ).symm
  exact Functor.Full.of_comp_faithful _ (ObjectProperty.ι _)

instance (X : C) [IsCardinalPresentable X κ] :
    (shrinkYoneda.{w}.flip.obj (op X)).IsCardinalAccessible κ where
  preservesColimitOfShape J _ _ := by
    have := preservesColimitsOfShape_of_isCardinalPresentable_of_essentiallySmall X κ J
    have := preservesColimitsOfShape_of_natIso (J := J)
      (shrinkYonedaFlipObjCompUliftFunctorIso X).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance : (toCardinalContinuous C κ).EssSurj where
  mem_essImage := by
    let P := (isCardinalPresentable C κ).FullSubcategory
    let cont := Functor.isCardinalContinuous Pᵒᵖ (Type w) κ
    intro (F : cont.FullSubcategory)
    obtain ⟨J, _, hJ, G, ι, ⟨h⟩⟩ :=
      Presheaf.exists_presentation_of_isCardinalContinuous.{w} (fun J _ hJ ↦ by
        have := isClosedUnderColimitsOfShape_isCardinalPresentable C hJ
        infer_instance) F.2
    let G₁ := G ⋙ ObjectProperty.ι _
    let G₂ := G ⋙ shrinkYoneda.{w}
    refine ⟨colimit G₁,
      ⟨(ObjectProperty.fullyFaithfulι _).preimageIso ?_⟩⟩
    --dsimp [toCardinalContinuous, Presheaf.restrictedShrinkYoneda]
    let c' : Cocone G₂ :=
      { pt := (isCardinalPresentable C κ).ι.op ⋙ shrinkYoneda.{w, v, u}.obj (colimit G₁)
        ι.app j :=
          shrinkYonedaMap (F := (isCardinalPresentable C κ).ι) (G.obj j) ≫
            Functor.whiskerLeft _ (shrinkYoneda.{w}.map (colimit.ι G₁ j))
        ι.naturality j j' f := by
          ext
          dsimp [shrinkYoneda]
          erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
          rw [EmbeddingLike.apply_eq_iff_eq]
          rw [← colimit.w G₁ f, ← Category.assoc]
          congr 1
          simp [G₁, G₂, shrinkYoneda]
          sorry } --rfl }
    have h' : IsColimit c' := evaluationJointlyReflectsColimits _ (fun ⟨X⟩ ↦ by
      have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
        (shrinkYoneda.{w}.flip.obj (op X.1)) κ J
      refine (IsColimit.equivOfNatIsoOfIso
        (NatIso.ofComponents
          (fun j ↦ (shrinkYonedaMapIso (isCardinalPresentable C κ).ι
            (G.obj j)).app _) (fun _ ↦ ?_)) _ _ ?_).2
        (isColimitOfPreserves
          (shrinkYoneda.{w}.flip.obj (op X.1)) (colimit.isColimit G₁))
      · ext
        simp [shrinkYoneda, shrinkYonedaMap, G₁, G₂]
        sorry --rfl
      · refine (Cocone.ext (Iso.refl _) (fun j ↦ ?_))
        simp [c', dsimp% (shrinkYonedaMapIso (isCardinalPresentable C κ).ι
          (G.obj j)).inv_hom_id_app_assoc (op X)])
    exact IsColimit.coconePointUniqueUpToIso h' h

instance : (toCardinalContinuous C κ).IsEquivalence where

@[simps! functor]
noncomputable def toCardinalContinuousEquivalence :
    C ≌ (Functor.isCardinalContinuous
      (isCardinalPresentable C κ).FullSubcategoryᵒᵖ (Type w) κ).FullSubcategory :=
  (toCardinalContinuous C κ).asEquivalence

include κ in
lemma hasLimitsOfSize : HasLimitsOfSize.{w, w} C :=
  Adjunction.has_limits_of_equivalence
    (IsCardinalLocallyPresentable.toCardinalContinuousEquivalence C κ).functor

include κ in
lemma hasFiniteLimits : HasFiniteLimits C := by
  have := hasLimitsOfSize C κ
  exact hasFiniteLimits_of_hasLimitsOfSize.{w, w} C

instance (J : Type w) [SmallCategory J] :
    IsCardinalLocallyPresentable (Jᵒᵖ ⥤ C) κ := by
  have := IsCardinalLocallyPresentable.hasFiniteLimits C κ
  infer_instance

end IsCardinalLocallyPresentable

namespace IsCardinalPresentable

instance (C : Type u) [Category.{v} C] [IsLocallyPresentable.{w} C] :
    HasLimitsOfSize.{w, w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact IsCardinalLocallyPresentable.hasLimitsOfSize C κ

instance (C : Type u) [Category.{v} C] [IsLocallyPresentable.{w} C] :
    HasFiniteLimits C :=
  hasFiniteLimits_of_hasLimitsOfSize.{w, w} C

end IsCardinalPresentable

end CategoryTheory

/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Presentable.Continuous
import Mathlib.CategoryTheory.Presentable.Dense

/-!
# The representation theorem

In this file, we show that if `C` is a locally `κ`-presentable category,
then `C` identifies to the category of `κ`-continuous presheaves on
the fullsubcategory of `κ`-presentable objects of `C`.

-/

universe w v v' u u'

namespace CategoryTheory

open Limits Opposite

namespace Functor

variable {C₁ C₂ C₃ C₄ : Type*} [Category C₁] [Category C₂] [Category C₃] [Category C₄]

@[simps!]
def whiskeringLeftObjCompWhiskeringRightObj (F : C₁ ⥤ C₂) (G : C₃ ⥤ C₄) :
    (whiskeringLeft C₁ C₂ C₃).obj F ⋙ (whiskeringRight C₁ C₃ C₄).obj G ≅
      (whiskeringRight C₂ C₃ C₄).obj G ⋙ (whiskeringLeft C₁ C₂ C₄).obj F :=
  NatIso.ofComponents (fun _ ↦ Functor.associator _ _ _)

end Functor

-- to be moved
namespace Presheaf

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  [LocallySmall.{w} D] (F : C ⥤ D)

noncomputable def shrinkYonedaCompWhiskeringRightUliftFunctorIso :
    shrinkYoneda.{w} (C := D) ⋙
      (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}) ≅
    uliftYoneda.{w} :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun Y ↦ (Equiv.ulift.trans (Equiv.trans (equivShrink _).symm Equiv.ulift.symm)).toIso) (by
    intro Y₁ Y₂ f
    ext g
    simp [uliftYoneda, shrinkYoneda])) (by
    intro X₁ X₂ f
    ext Y g
    simp [uliftYoneda, shrinkYoneda])

noncomputable def restrictedShrinkYoneda : D ⥤ Cᵒᵖ ⥤ Type w :=
  shrinkYoneda ⋙ (Functor.whiskeringLeft _ _ _).obj F.op

open Functor in
noncomputable def restrictedShrinkYonedaCompULiftIso :
    restrictedShrinkYoneda.{w} F ⋙
      (Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}) ≅
        restrictedULiftYoneda.{w} F :=
  associator _ _ _ ≪≫
    isoWhiskerLeft _ (whiskeringLeftObjCompWhiskeringRightObj _ _) ≪≫
    (associator _ _ _).symm ≪≫
    isoWhiskerRight shrinkYonedaCompWhiskeringRightUliftFunctorIso.{w} _

variable [F.IsDense]

instance : (restrictedShrinkYoneda.{w} F).Faithful := by
  have := Functor.Faithful.of_iso (restrictedShrinkYonedaCompULiftIso.{w} F).symm
  exact Functor.Faithful.of_comp _ ((Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}))

instance : (restrictedShrinkYoneda.{w} F).Full := by
  have := Functor.Full.of_iso (restrictedShrinkYonedaCompULiftIso.{w} F).symm
  exact Functor.Full.of_comp_faithful _
    ((Functor.whiskeringRight _ _ _).obj (uliftFunctor.{v', w}))

end Presheaf

namespace IsCardinalLocallyPresentable

variable (C : Type u) [Category.{v} C] (κ : Cardinal.{w}) [Fact κ.IsRegular]
  [IsCardinalLocallyPresentable C κ]

open Functor in
noncomputable def toCardinalContinuous :
    C ⥤ (Functor.isCardinalContinuous
      (isCardinalPresentable C κ).FullSubcategoryᵒᵖ (Type w) κ).FullSubcategory :=
  ObjectProperty.lift _ (Presheaf.restrictedShrinkYoneda.{w} (ObjectProperty.ι _)) (fun X ↦ by
    rw [isCardinalContinuous_iff]
    intro J _ _
    dsimp [Presheaf.restrictedShrinkYoneda]
    have : (isCardinalPresentable C κ).IsClosedUnderColimitsOfShape Jᵒᵖ :=
      isClosedUnderColimitsOfShape_isCardinalPresentable _ (by simpa)
    have : PreservesLimitsOfShape J (isCardinalPresentable C κ).ι.op :=
      preservesLimitsOfShape_op _ _
    infer_instance)

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
      (shrinkYonedaFlipObjCompUliftFunctorIso.{w} X).symm
    exact preservesColimitsOfShape_of_reflects_of_preserves _ uliftFunctor.{v}

instance : (toCardinalContinuous C κ).EssSurj where
  mem_essImage := by
    let P := (isCardinalPresentable C κ).FullSubcategory
    let cont := Functor.isCardinalContinuous Pᵒᵖ (Type w) κ
    intro (F : cont.FullSubcategory)
    obtain ⟨J, _, hJ, G, ι, ⟨h⟩⟩ :=
      Presheaf.exists_presentation_of_isCardinalContinuous.{w} (fun J _ hJ ↦ by
        have := isClosedUnderColimitsOfShape_isCardinalPresentable C hJ
        infer_instance) F.2
    let G₁ := (G ⋙ CostructuredArrow.proj _ _ ⋙ ObjectProperty.ι _)
    let G₂ := G ⋙ CostructuredArrow.proj _ _ ⋙ shrinkYoneda.{w}
    refine ⟨colimit G₁,
      ⟨(ObjectProperty.fullyFaithfulι _).preimageIso ?_⟩⟩
    dsimp [toCardinalContinuous, Presheaf.restrictedShrinkYoneda]
    let c' : Cocone G₂ :=
      { pt := (isCardinalPresentable C κ).ι.op ⋙ shrinkYoneda.{w, v, u}.obj (colimit G₁)
        ι.app j :=
          shrinkYonedaMap (F := (isCardinalPresentable C κ).ι) (G.obj j).left ≫
            Functor.whiskerLeft _ (shrinkYoneda.{w}.map (colimit.ι G₁ j))
        ι.naturality j j' f := by
          ext
          dsimp [shrinkYoneda]
          simp only [Equiv.symm_apply_apply, EmbeddingLike.apply_eq_iff_eq]
          rw [← colimit.w G₁ f, ← Category.assoc]
          congr 1
          simp [G₁, G₂, shrinkYoneda]
          rfl }
    have h' : IsColimit c' := evaluationJointlyReflectsColimits _ (fun ⟨X⟩ ↦ by
      have := Functor.preservesColimitsOfShape_of_isCardinalAccessible
        (shrinkYoneda.{w}.flip.obj (op X.1)) κ J
      refine IsColimit.ofIsoColimit (isColimitOfPreserves
        (shrinkYoneda.{w}.flip.obj (op X.1)) (colimit.isColimit G₁))
        (Cocones.ext (Iso.refl _) (fun j ↦ ?_))
      ext f
      obtain ⟨f, rfl⟩ := shrinkYonedaObjObjEquiv.symm.surjective f
      simp [c']
      apply congr_arg
      erw [Equiv.symm_apply_apply]
      rfl)
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

end IsCardinalLocallyPresentable

namespace IsCardinalPresentable

instance (C : Type u) [Category.{v} C] [IsLocallyPresentable.{w} C] :
    HasLimitsOfSize.{w, w} C := by
  obtain ⟨κ, _, _⟩ := IsLocallyPresentable.exists_cardinal.{w} C
  exact IsCardinalLocallyPresentable.hasLimitsOfSize C κ

end IsCardinalPresentable

end CategoryTheory

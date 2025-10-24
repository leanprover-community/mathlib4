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

open Limits

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

instance : (toCardinalContinuous C κ).EssSurj where
  mem_essImage := by
    let P := (isCardinalPresentable C κ).FullSubcategory
    let cont := Functor.isCardinalContinuous Pᵒᵖ (Type w) κ
    intro (F : cont.FullSubcategory)
    -- need to know that the presheaf `F.obj` is a `κ`-filtered colimit
    -- of representable presheaves, and for this it suffices to
    -- know that the "canonical" diagram is `κ`-filtered, and this
    -- shall follow from the continuity of `F` and the
    -- existence of `κ`-bounded colimits in `P`
    sorry


instance : (toCardinalContinuous C κ).IsEquivalence where

@[simps! functor]
noncomputable def toCardinalContinuousEquivalence :
    C ≌ (Functor.isCardinalContinuous
      (isCardinalPresentable C κ).FullSubcategoryᵒᵖ (Type w) κ).FullSubcategory :=
  (toCardinalContinuous C κ).asEquivalence

end IsCardinalLocallyPresentable

end CategoryTheory

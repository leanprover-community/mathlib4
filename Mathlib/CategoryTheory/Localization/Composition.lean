/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Localization.LocalizerMorphism

/-!
# Composition of localization functors

Given two composable functors `L₁ : C₁ ⥤ C₂` and `L₂ : C₂ ⥤ C₃`, it is shown
in this file that under some suitable conditions on `W₁ : MorphismProperty C₁`
`W₂ : MorphismProperty C₂` and `W₃ : MorphismProperty C₁`, then
if `L₁ : C₁ ⥤ C₂` is a localization functor for `W₁`,
then the composition `L₁ ⋙ L₂ : C₁ ⥤ C₃` is a localization functor for `W₃`
if and only if `L₂ : C₂ ⥤ C₃` is a localization functor for `W₂`.
The two implications are the lemmas `Functor.IsLocalization.comp` and
`Functor.IsLocalization.of_comp`.

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {E : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} E]
  {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
namespace Localization

/-- Under some conditions on the `MorphismProperty`, functors satisfying the strict
universal property of the localization are stable under composition -/
def StrictUniversalPropertyFixedTarget.comp
    (h₁ : StrictUniversalPropertyFixedTarget L₁ W₁ E)
    (h₂ : StrictUniversalPropertyFixedTarget L₂ W₂ E)
    (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
    (hW₁₃ : W₁ ⊆ W₃) (hW₂₃ : W₂ ⊆ W₃.map L₁) :
    StrictUniversalPropertyFixedTarget (L₁ ⋙ L₂) W₃ E where
  inverts := hW₃
  lift F hF := by
    have hF₁ : W₁.IsInvertedBy F := fun _ _ f hf => hF _ (hW₁₃ _ hf)
    exact h₂.lift (h₁.lift F hF₁) (fun _ _ f hf => by
      obtain ⟨_, _, g, hg, ⟨iso⟩⟩ := hW₂₃ _ hf
      refine' ((MorphismProperty.RespectsIso.isomorphisms E).arrow_mk_iso_iff _).1 (hF _ hg)
      exact (Arrow.isoOfNatIso (eqToIso (h₁.fac F hF₁).symm) (Arrow.mk g)) ≪≫
        ((h₁.lift F hF₁).mapArrow.mapIso iso))
  fac F hF := by rw [Functor.assoc, h₂.fac, h₁.fac]
  uniq F₁ F₂ h := h₂.uniq _ _ (h₁.uniq _ _ (by simpa only [Functor.assoc] using h))

end Localization

open Localization

namespace Functor

namespace IsLocalization

variable (L₁ W₁ L₂ W₂)


lemma comp [L₁.IsLocalization W₁] [L₂.IsLocalization W₂]
    (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
    (hW₁₃ : W₁ ⊆ W₃) (hW₂₃ : W₂ ⊆ W₃.map L₁) :
    (L₁ ⋙ L₂).IsLocalization W₃ := by
  -- the proof proceeds by replacing the case of the composition `L₁ ⋙ L₂`
  -- by the composition `L₁' ⋙ L₂'` where `L₁'` and `L₂`' are the constructed
  -- localized categories, which both satisfy the strict universal property of
  -- the localization `StrictUniversalPropertyFixedTarget`
  let L₁' := W₁.Q
  let E₂ := Localization.uniq L₁' L₁ W₁
  let W₂' := W₂.map E₂.inverse
  let L₂' := W₂'.Q
  have hW₂₃' : W₂' ⊆ W₃.map L₁' := (MorphismProperty.monotone_map _ _ E₂.inverse hW₂₃).trans (by
    apply subset_of_eq
    rw [← W₃.map_eq_of_iso (show L₁' ⋙ E₂.functor ≅ L₁ from compUniqFunctor L₁' L₁ W₁),
      MorphismProperty.map_map]
    exact W₃.map_eq_of_iso (Functor.associator _ _ _ ≪≫
      isoWhiskerLeft L₁' E₂.unitIso.symm ≪≫ Functor.rightUnitor _))
  let Φ : LocalizerMorphism W₂' W₂.isoClosure :=
  { functor := E₂.functor
    map := by rw [W₂.isoClosure_inverseImage_equivalence_functor E₂] }
  haveI : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ
      (by
        rw [W₂.isoClosure_subset_iff _ (W₂'.map_respectsIso Φ.functor),
          MorphismProperty.map_map, W₂.map_eq_of_iso E₂.counitIso, W₂.map_id_eq_isoClosure]
        exact W₂.subset_isoClosure)
  let iso : (L₁' ⋙ L₂') ⋙ Φ.localizedFunctor W₂'.Q L₂ ≅ L₁ ⋙ L₂ :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (Iso.symm (Φ.catCommSq W₂'.Q L₂).iso) ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (compUniqFunctor L₁' L₁ W₁) _
  have hW₃' : W₃.IsInvertedBy (L₁' ⋙ L₂') :=  by
      simpa only [← MorphismProperty.IsInvertedBy.iff_comp _ _ (Φ.localizedFunctor W₂'.Q L₂),
        MorphismProperty.IsInvertedBy.iff_of_iso W₃ iso] using hW₃
  haveI : (L₁' ⋙ L₂').IsLocalization W₃ :=
    IsLocalization.mk' _ _
      (StrictUniversalPropertyFixedTarget.comp (strictUniversalPropertyFixedTargetQ W₁ _)
        (strictUniversalPropertyFixedTargetQ W₂' _) W₃ hW₃' hW₁₃ hW₂₃')
      (StrictUniversalPropertyFixedTarget.comp (strictUniversalPropertyFixedTargetQ W₁ _)
        (strictUniversalPropertyFixedTargetQ W₂' _) W₃ hW₃' hW₁₃ hW₂₃')
  exact IsLocalization.of_equivalence_target (L₁' ⋙ L₂') W₃ (L₁ ⋙ L₂)
    (asEquivalence (Φ.localizedFunctor W₂'.Q L₂)) iso

lemma of_comp (W₃ : MorphismProperty C₁)
    [L₁.IsLocalization W₁] [(L₁ ⋙ L₂).IsLocalization W₃]
    (hW₁₃ : W₁ ⊆ W₃) (hW₂₃ : W₂ = W₃.map L₁) :
      L₂.IsLocalization W₂ := by
    have : (L₁ ⋙ W₂.Q).IsLocalization W₃ :=
      comp L₁ W₂.Q W₁ W₂ W₃ (fun X Y f hf => Localization.inverts W₂.Q W₂ _
        (by simpa only [hW₂₃] using W₃.map_mem_map _ _ hf))
        hW₁₃ (by rw [hW₂₃, MorphismProperty.subset_iff_le])
    exact IsLocalization.of_equivalence_target W₂.Q W₂ L₂
      (Localization.uniq (L₁ ⋙ W₂.Q) (L₁ ⋙ L₂) W₃)
      (liftNatIso L₁ W₁ _ _ _ _
        ((Functor.associator _ _ _).symm ≪≫
          Localization.compUniqFunctor (L₁ ⋙ W₂.Q) (L₁ ⋙ L₂) W₃))

end IsLocalization

end Functor

end CategoryTheory

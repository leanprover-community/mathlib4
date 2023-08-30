import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.Localization.LocalizerMorphism
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.ReflectsIso

namespace CategoryTheory

namespace Localization

/-- Under some conditions on the `MorphismProperty`, functors satisfying the strict
universal property of the localization are stable under composition -/
def StrictUniversalPropertyFixedTarget.comp
  {C₁ C₂ C₃ E : Type _} [Category C₁] [Category C₂] [Category C₃] [Category E]
  {L₁ : C₁ ⥤ C₂} {L₂ : C₂ ⥤ C₃} {W₁ : MorphismProperty C₁} {W₂ : MorphismProperty C₂}
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

lemma comp {C₁ C₂ C₃ : Type _} [Category C₁] [Category C₂] [Category C₃]
  (L₁ : C₁ ⥤ C₂) (W₁ : MorphismProperty C₁) [L₁.IsLocalization W₁]
  (L₂ : C₂ ⥤ C₃) (W₂ : MorphismProperty C₂) [L₂.IsLocalization W₂]
  (W₃ : MorphismProperty C₁) (hW₃ : W₃.IsInvertedBy (L₁ ⋙ L₂))
  (hW₁₃ : W₁ ⊆ W₃) (hW₂₃ : W₂ ⊆ W₃.map L₁) :
    (L₁ ⋙ L₂).IsLocalization W₃ := by
  let L₁' := W₁.Q
  let E₂ := Localization.uniq L₁' L₁ W₁
  let W₂' := W₂.isoClosure.inverseImage E₂.functor
  let L₂' := W₂'.Q
  have hW₂₃' : W₂' ⊆ W₃.map L₁' := fun _ _ f => by
    rintro ⟨_, _, f', hf', ⟨e⟩⟩
    obtain ⟨_, _, g, hg, ⟨e'⟩⟩ := hW₂₃ _ hf'
    exact ⟨_, _, g, hg, ⟨(E₂.functor.mapArrow).preimageIso
      (Arrow.isoOfNatIso (compUniqFunctor L₁' L₁ W₁) (Arrow.mk g) ≪≫ e' ≪≫ e)⟩⟩
  haveI : L₂.IsLocalization W₂.isoClosure := by
    refine' of_equivalence_source L₂ W₂ L₂ W₂.isoClosure Equivalence.refl _ _ L₂.leftUnitor
    . intro _ _ f hf
      exact ⟨_, _, f, ⟨_, _, f, hf, ⟨Iso.refl _⟩⟩, ⟨Iso.refl _⟩⟩
    . intro _ _ f ⟨_, _, f', hf', ⟨e⟩⟩
      exact ((MorphismProperty.RespectsIso.isomorphisms _).arrow_mk_iso_iff
        (L₂.mapArrow.mapIso e)).1 (Localization.inverts L₂ W₂ f' hf')
  let Φ : LocalizerMorphism W₂' W₂.isoClosure :=
  { functor := E₂.functor
    map := by rw [MorphismProperty.subset_iff_le] }
  let iso : (L₁' ⋙ L₂') ⋙ Φ.localizedFunctor W₂'.Q L₂ ≅ L₁ ⋙ L₂ :=
    Functor.associator _ _ _ ≪≫
      isoWhiskerLeft _ (Iso.symm (Φ.catCommSq W₂'.Q L₂).iso) ≪≫
      (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight (compUniqFunctor L₁' L₁ W₁) _
  haveI : Φ.IsLocalizedEquivalence :=
    LocalizerMorphism.IsLocalizedEquivalence.of_equivalence Φ
      (by rw [MorphismProperty.map_inverseImage_eq_of_isEquivalence W₂.isoClosure
        W₂.isoClosure_respectsIso Φ.functor, MorphismProperty.subset_iff_le])
  have hW₃' : W₃.IsInvertedBy (L₁' ⋙ L₂') := fun _ _ f hf => by
    haveI : IsIso ((Φ.localizedFunctor W₂'.Q L₂).map ((L₁' ⋙ L₂').map f)) :=
      ((MorphismProperty.RespectsIso.isomorphisms _).arrow_iso_iff
        (((mapArrowFunctor _ _).mapIso iso).app (Arrow.mk f))).2 (hW₃ _ hf)
    exact isIso_of_reflects_iso _ (Φ.localizedFunctor W₂'.Q L₂)
  haveI : (L₁' ⋙ L₂').IsLocalization W₃ :=
    IsLocalization.mk' _ _
      (StrictUniversalPropertyFixedTarget.comp (strictUniversalPropertyFixedTargetQ W₁ _)
        (strictUniversalPropertyFixedTargetQ W₂' _) W₃ hW₃' hW₁₃ hW₂₃')
      (StrictUniversalPropertyFixedTarget.comp (strictUniversalPropertyFixedTargetQ W₁ _)
        (strictUniversalPropertyFixedTargetQ W₂' _) W₃ hW₃' hW₁₃ hW₂₃')
  exact IsLocalization.of_equivalence_target (L₁' ⋙ L₂') W₃ (L₁ ⋙ L₂)
    (asEquivalence (Φ.localizedFunctor W₂'.Q L₂)) iso

end IsLocalization

end Functor

end CategoryTheory

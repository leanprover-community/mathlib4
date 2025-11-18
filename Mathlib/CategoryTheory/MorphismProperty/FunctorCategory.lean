/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.MorphismProperty.Retract
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.CategoryTheory.MorphismProperty.TransfiniteComposition

/-!
# Stability properties of morphism properties on functor categories

Given `W : MorphismProperty C` and a category `J`, we study the
stability properties of `W.functorCategory J : MorphismProperty (J ⥤ C)`.

Under suitable assumptions, we also show that if monomorphisms
in `C` are stable under transfinite compositions, then the same
holds in the category `J ⥤ C`.

-/

universe v v' v'' u u' u''

namespace CategoryTheory

open Limits

namespace MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

instance [W.IsStableUnderRetracts] (J : Type u'') [Category.{v''} J] :
    (W.functorCategory J).IsStableUnderRetracts where
  of_retract hfg hg j :=
    W.of_retract (hfg.map ((evaluation _ _).obj j)) (hg j)

variable {W}

instance IsStableUnderLimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderLimitsOfShape K]
    (J : Type u'') [Category.{v''} J] [HasLimitsOfShape K C] :
    (W.functorCategory J).IsStableUnderLimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.limitsOfShape_le _
      (limitsOfShape.mk' (X₁ ⋙ (evaluation _ _ ).obj j) (X₂ ⋙ (evaluation _ _ ).obj j)
      _ _ (isLimitOfPreserves _ hc₁) (isLimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k ↦ hf k j) (φ.app j) (fun k ↦ congr_app (hφ k) j))

instance IsStableUnderColimitsOfShape.functorCategory
    {K : Type u'} [Category.{v'} K] [W.IsStableUnderColimitsOfShape K]
    (J : Type u'') [Category.{v''} J] [HasColimitsOfShape K C] :
    (W.functorCategory J).IsStableUnderColimitsOfShape K where
  condition X₁ X₂ _ _ hc₁ hc₂ f hf φ hφ j :=
    MorphismProperty.colimitsOfShape_le _
      (colimitsOfShape.mk' (X₁ ⋙ (evaluation _ _ ).obj j) (X₂ ⋙ (evaluation _ _ ).obj j)
      _ _ (isColimitOfPreserves _ hc₁) (isColimitOfPreserves _ hc₂) (Functor.whiskerRight f _)
      (fun k ↦ hf k j) (φ.app j) (fun k ↦ congr_app (hφ k) j))

instance [W.IsStableUnderBaseChange] (J : Type u'') [Category.{v''} J] [HasPullbacks C] :
    (W.functorCategory J).IsStableUnderBaseChange where
  of_isPullback sq hr j :=
    W.of_isPullback (sq.map ((evaluation _ _).obj j)) (hr j)

instance [W.IsStableUnderCobaseChange] (J : Type u'') [Category.{v''} J] [HasPushouts C] :
    (W.functorCategory J).IsStableUnderCobaseChange where
  of_isPushout sq hr j :=
    W.of_isPushout (sq.map ((evaluation _ _).obj j)) (hr j)

instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [W.IsStableUnderTransfiniteCompositionOfShape K] (J : Type u'') [Category.{v''} J]
    [HasIterationOfShape K C] :
    (W.functorCategory J).IsStableUnderTransfiniteCompositionOfShape K where
  le := by
    rintro X Y f ⟨hf⟩ j
    have : W.functorCategory J ≤ W.inverseImage ((evaluation _ _).obj j) := fun _ _ _ h ↦ h _
    exact W.transfiniteCompositionsOfShape_le K _ ⟨(hf.ofLE this).map⟩

variable (J : Type u'') [Category.{v''} J]

lemma functorCategory_isomorphisms :
    (isomorphisms C).functorCategory J = isomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, isomorphisms.iff, NatTrans.isIso_iff_isIso_app]

lemma functorCategory_monomorphisms [HasPullbacks C] :
    (monomorphisms C).functorCategory J = monomorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, monomorphisms.iff, NatTrans.mono_iff_mono_app]

lemma functorCategory_epimorphisms [HasPushouts C] :
    (epimorphisms C).functorCategory J = epimorphisms (J ⥤ C) := by
  ext _ _ f
  simp only [functorCategory, epimorphisms.iff, NatTrans.epi_iff_epi_app]

instance (K : Type u') [LinearOrder K] [SuccOrder K] [OrderBot K] [WellFoundedLT K]
    [(monomorphisms C).IsStableUnderTransfiniteCompositionOfShape K]
    [HasPullbacks C] (J : Type u'') [Category.{v''} J] [HasIterationOfShape K C] :
    (monomorphisms (J ⥤ C)).IsStableUnderTransfiniteCompositionOfShape K := by
  rw [← functorCategory_monomorphisms]
  infer_instance

end MorphismProperty

end CategoryTheory

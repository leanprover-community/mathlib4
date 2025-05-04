/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.CategoryTheory.MorphismProperty.Comma
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Etale morphisms

A morphism of schemes `f : X ⟶ Y` is étale if it is smooth of relative dimension zero. We
also define the category of schemes étale over `X`.

-/

universe t u

universe u₂ u₁ v₂ v₁

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

/-- A morphism of schemes is étale if it is smooth of relative dimension zero. -/
abbrev IsEtale {X Y : Scheme.{u}} (f : X ⟶ Y) := IsSmoothOfRelativeDimension 0 f

namespace IsEtale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance [IsEtale f] : IsSmooth f :=
  IsSmoothOfRelativeDimension.isSmooth 0 f

instance : IsStableUnderBaseChange @IsEtale :=
  isSmoothOfRelativeDimension_isStableUnderBaseChange 0

open RingHom in
instance (priority := 900) [IsEtale f] : FormallyUnramified f where
  formallyUnramified_of_affine_subset U V e := by
    have : Locally (IsStandardSmoothOfRelativeDimension 0) (f.appLE (↑U) (↑V) e).hom :=
      HasRingHomProperty.appLE (P := @IsSmoothOfRelativeDimension 0) _ inferInstance ..
    have : Locally RingHom.FormallyUnramified (f.appLE U V e).hom := by
      apply locally_of_locally _ this
      intro R S _ _ f hf
      algebraize [f]
      rw [RingHom.FormallyUnramified]
      have : Algebra.IsStandardSmoothOfRelativeDimension 0 R S := hf
      infer_instance
    rwa [← RingHom.locally_iff_of_localizationSpanTarget
      FormallyUnramified.respectsIso FormallyUnramified.ofLocalizationSpanTarget]

instance : MorphismProperty.HasOfPostcompProperty
    @IsEtale (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
  exact inferInstanceAs <| IsEtale (pullback.diagonal f)

/-- If `f ≫ g` is etale and `g` unramified, then `f` is étale. -/
lemma of_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [IsEtale (f ≫ g)] [LocallyOfFiniteType g]
    [FormallyUnramified g] : IsEtale f :=
  of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›

instance : MorphismProperty.HasOfPostcompProperty @IsEtale @IsEtale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @IsEtale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

end IsEtale

namespace Scheme

/-- The category `Etale X` is the category of schemes étale over `X`. -/
def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @IsEtale ⊤ X

variable (X : Scheme.{u})

instance : Category X.Etale :=
  inferInstanceAs <| Category (MorphismProperty.Over @IsEtale ⊤ X)

/-- The forgetful functor from schemes étale over `X` to schemes over `X`. -/
def Etale.forget : X.Etale ⥤ Over X :=
  MorphismProperty.Over.forget @IsEtale ⊤ X

/-- The forgetful functor from schemes étale over `X` to schemes over `X` is fully faithful. -/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

instance : (Etale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (Etale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful

instance : HasPullbacks X.Etale := by
  unfold Etale
  infer_instance

end Scheme

end AlgebraicGeometry

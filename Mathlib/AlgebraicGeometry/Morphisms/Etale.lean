/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
public import Mathlib.CategoryTheory.MorphismProperty.Comma
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.CategoryTheory.Limits.MorphismProperty

/-!

# Étale morphisms

A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, the induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale.

## Main results

- `AlgebraicGeometry.Etale.iff_smoothOfRelativeDimension_zero`: Etale is equivalent to
  smooth of relative dimension `0`.

-/

@[expose] public section

universe t u

universe u₂ u₁ v₂ v₁

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is étale if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is étale. -/
@[mk_iff]
class Etale {X Y : Scheme.{u}} (f : X ⟶ Y) : Prop where
  etale_appLE (f) :
    ∀ {U : Y.Opens} (_ : IsAffineOpen U) {V : X.Opens} (_ : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U),
      (f.appLE U V e).hom.Etale

alias Scheme.Hom.etale_appLE := Etale.etale_appLE

@[deprecated (since := "2026-02-09")] alias IsEtale := Etale

namespace Etale

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The property of scheme morphisms `Etale` is associated with the ring
homomorphism property `Etale`. -/
instance : HasRingHomProperty @Etale RingHom.Etale where
  isLocal_ringHomProperty := RingHom.Etale.propertyIsLocal
  eq_affineLocally' := by
    ext X Y f
    rw [etale_iff, affineLocally_iff_forall_isAffineOpen]

/-- Being étale is multiplicative. -/
instance : MorphismProperty.IsMultiplicative @Etale :=
  HasRingHomProperty.isMultiplicative RingHom.Etale.stableUnderComposition
    RingHom.Etale.containsIdentities

/-- The composition of étale morphisms is étale. -/
instance etale_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale f] [Etale g] :
    Etale (f ≫ g) :=
  MorphismProperty.comp_mem _ f g ‹Etale f› ‹Etale g›

/-- Etale is stable under base change. -/
instance etale_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseChange @Etale :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.Etale.isStableUnderBaseChange

/-- Open immersions are étale. -/
instance (priority := 900) [IsOpenImmersion f] : Etale f :=
  HasRingHomProperty.of_isOpenImmersion RingHom.Etale.containsIdentities

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale g] :
    Etale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale f] :
    Etale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [Etale f] : Etale (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance (f : X ⟶ Y) (U : X.Opens) (V : Y.Opens) (e) [Etale f] :
    Etale (f.resLE V U e) := by
  delta Scheme.Hom.resLE; infer_instance

lemma eq_smoothOfRelativeDimension_zero : @Etale = @SmoothOfRelativeDimension 0 := by
  apply HasRingHomProperty.ext
  introv
  have : @RingHom.Etale = @RingHom.IsStandardSmoothOfRelativeDimension 0 := by
    ext; apply RingHom.etale_iff_isStandardSmoothOfRelativeDimension_zero
  rw [← this, RingHom.locally_iff_of_localizationSpanTarget]
  · exact RingHom.Etale.respectsIso
  · exact RingHom.Etale.ofLocalizationSpanTarget

lemma iff_smoothOfRelativeDimension_zero : Etale f ↔ SmoothOfRelativeDimension 0 f := by
  rw [eq_smoothOfRelativeDimension_zero]

instance [Etale f] : SmoothOfRelativeDimension 0 f := by
  rwa [← iff_smoothOfRelativeDimension_zero]

instance (priority := low) [Etale f] : Smooth f :=
  SmoothOfRelativeDimension.smooth 0 f

open RingHom in
instance (priority := 900) [Etale f] : FormallyUnramified f where
  formallyUnramified_appLE {_} hU {_} hV e :=
    (f.etale_appLE hU hV e).formallyUnramified

instance : MorphismProperty.HasOfPostcompProperty
    @Etale (@LocallyOfFiniteType ⊓ @FormallyUnramified) := by
  rw [MorphismProperty.hasOfPostcompProperty_iff_le_diagonal]
  intro X Y f ⟨hft, hfu⟩
  exact inferInstanceAs <| Etale (pullback.diagonal f)

/-- If `f ≫ g` is étale and `g` unramified, then `f` is étale. -/
lemma of_comp {Z : Scheme.{u}} (g : Y ⟶ Z) [Etale (f ≫ g)] [LocallyOfFiniteType g]
    [FormallyUnramified g] : Etale f :=
  of_postcomp _ (W' := @LocallyOfFiniteType ⊓ @FormallyUnramified) f g ⟨‹_›, ‹_›⟩ ‹_›

instance : MorphismProperty.HasOfPostcompProperty @Etale @Etale := by
  apply MorphismProperty.HasOfPostcompProperty.of_le (W := @Etale)
    (Q := (@LocallyOfFiniteType ⊓ @FormallyUnramified))
  intro X Y f hf
  constructor <;> infer_instance

end Etale

namespace Scheme

/-- The category `Etale X` is the category of schemes étale over `X`. -/
protected def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @Etale ⊤ X

variable (X : Scheme.{u})

instance : Category X.Etale :=
  inferInstanceAs <| Category (MorphismProperty.Over @Etale ⊤ X)

/-- The forgetful functor from schemes étale over `X` to schemes over `X`. -/
def Etale.forget : X.Etale ⥤ Over X :=
  MorphismProperty.Over.forget @Etale ⊤ X

/-- The forgetful functor from schemes étale over `X` to schemes over `X` is fully faithful. -/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

instance : (Etale.forget X).Full :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Full
instance : (Etale.forget X).Faithful :=
  inferInstanceAs <| (MorphismProperty.Comma.forget _ _ _ _ _).Faithful

instance : HasPullbacks X.Etale := by
  unfold Scheme.Etale
  infer_instance

end Scheme

end AlgebraicGeometry

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

set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale g] :
    Etale (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [Etale f] :
    Etale (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
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

set_option backward.isDefEq.respectTransparency.types false in
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

lemma iff_flat_and_formallyUnramified {f : X ⟶ Y} :
    Etale f ↔ Flat f ∧ FormallyUnramified f ∧ LocallyOfFinitePresentation f := by
  rw [etale_iff, flat_iff, formallyUnramified_iff, locallyOfFinitePresentation_iff]
  grind [RingHom.Etale.iff_flat_and_formallyUnramified]

lemma of_formallyUnramified_of_flat [Flat f] [FormallyUnramified f]
    [LocallyOfFinitePresentation f] :
    Etale f := by
  rw [Etale.iff_flat_and_formallyUnramified]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

end Etale

namespace Scheme

set_option backward.isDefEq.respectTransparency.types false in
/-- The category `Etale X` is the category of schemes étale over `X`. -/
protected def Etale (X : Scheme.{u}) : Type _ := MorphismProperty.Over @Etale ⊤ X
deriving Category, HasPullbacks, HasFiniteLimits

variable (X : Scheme.{u})

set_option backward.defeqAttrib.useBackward true in
instance (Y : X.Etale) : dsimp% Etale Y.hom := Y.prop

set_option backward.isDefEq.respectTransparency.types false in
instance {X : Scheme.{u}} {Z Y : X.Etale} (f : Z ⟶ Y) : Etale f.left := by
  have : Etale (f.left ≫ Y.hom) := by rw [CategoryTheory.Over.w]; infer_instance
  exact Etale.of_comp f.left Y.hom

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from schemes étale over `X` to schemes over `X`. -/
def Etale.forget : X.Etale ⥤ Over X :=
  MorphismProperty.Over.forget @Etale ⊤ X

set_option backward.isDefEq.respectTransparency.types false in
/-- The forgetful functor from schemes étale over `X` to schemes over `X` is fully faithful. -/
def Etale.forgetFullyFaithful : (Etale.forget X).FullyFaithful :=
  MorphismProperty.Comma.forgetFullyFaithful _ _ _

-- Note: using `deriving Functor.Full/Faithful` in the declaration of `Etale.forget`
-- would "succeed", but it seems it would fail to create the next two instances
instance : (Etale.forget X).Full :=
  (Etale.forgetFullyFaithful X).full

instance : (Etale.forget X).Faithful :=
  (Etale.forgetFullyFaithful X).faithful

variable {X} in
/-- Constructor for objects in the étale site of a scheme `X`: it takes
an étale morphism `f : Y ⟶ X` as an input. -/
abbrev Etale.mk {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] : X.Etale :=
  MorphismProperty.Over.mk _ f inferInstance

variable {X} in
@[simp]
lemma Etale.forget_mk {Y : Scheme.{u}} (f : Y ⟶ X) [Etale f] :
    (Etale.forget X).obj (.mk f) = Over.mk f := rfl

@[simp]
lemma Etale.forget_obj_left (Y : X.Etale) :
    ((Etale.forget X).obj Y).left = Y.left := rfl

@[simp]
lemma Etale.forget_obj_hom (Y : X.Etale) :
    ((Etale.forget X).obj Y).hom = Y.hom := rfl

instance (Y : X.Etale) : Etale (Y.left ↘ X) := Y.prop

/-- Induction principle for the objects of the small étale site of a scheme. -/
@[elab_as_elim, cases_eliminator, induction_eliminator]
def Etale.rec {motive : X.Etale → Sort*}
    (mk : ∀ (Y : Scheme.{u}) (f : Y ⟶ X) (_ : Etale f), motive (Etale.mk f))
    (T : X.Etale) :
    motive T :=
  mk _ _ T.prop

set_option backward.isDefEq.respectTransparency.types false in
instance : PreservesFiniteLimits (Etale.forget X) :=
  inferInstanceAs (PreservesFiniteLimits (MorphismProperty.Over.forget _ ⊤ X))

end Scheme

end AlgebraicGeometry

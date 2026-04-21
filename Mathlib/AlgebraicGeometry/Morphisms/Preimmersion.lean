/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.SurjectiveOnStalks

/-!

# Preimmersions of schemes

A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of topological spaces
is an embedding and the induced morphisms of stalks are all surjective. This is not a concept seen
in the literature but it is useful for generalizing results on immersions to other maps including
`Spec 𝒪_{X, x} ⟶ X` and inclusions of fibers `κ(x) ×ₓ Y ⟶ Y`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe v u

open CategoryTheory Topology

namespace AlgebraicGeometry

/-- A morphism of schemes `f : X ⟶ Y` is a preimmersion if the underlying map of
topological spaces is an embedding and the induced morphisms of stalks are all surjective. -/
@[mk_iff]
class IsPreimmersion {X Y : Scheme} (f : X ⟶ Y) : Prop extends SurjectiveOnStalks f where
  isEmbedding (f) : IsEmbedding f

alias Scheme.Hom.isEmbedding := IsPreimmersion.isEmbedding

@[deprecated (since := "2026-01-20")] alias IsPreimmersion.base_embedding := Scheme.Hom.isEmbedding

lemma isPreimmersion_eq_inf :
    @IsPreimmersion = (@SurjectiveOnStalks ⊓ topologically IsEmbedding : MorphismProperty _) := by
  ext
  rw [isPreimmersion_iff]
  rfl

namespace IsPreimmersion

instance : IsZariskiLocalAtTarget @IsPreimmersion :=
  isPreimmersion_eq_inf ▸ inferInstance

instance (priority := 900) {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] : IsPreimmersion f where
  isEmbedding := f.isOpenEmbedding.isEmbedding
  stalkMap_surjective _ := (ConcreteCategory.bijective_of_isIso _).2

instance : MorphismProperty.IsMultiplicative @IsPreimmersion where
  id_mem _ := inferInstance
  comp_mem f g _ _ := ⟨g.isEmbedding.comp f.isEmbedding⟩

instance comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion f]
    [IsPreimmersion g] : IsPreimmersion (f ≫ g) :=
  MorphismProperty.IsStableUnderComposition.comp_mem f g inferInstance inferInstance

instance (priority := 900) {X Y} (f : X ⟶ Y) [IsPreimmersion f] : Mono f :=
  SurjectiveOnStalks.mono_of_injective f.isEmbedding.injective

theorem of_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g]
    [IsPreimmersion (f ≫ g)] : IsPreimmersion f where
  isEmbedding := by
    have h := (f ≫ g).isEmbedding
    rwa [← g.isEmbedding.of_comp_iff]
  stalkMap_surjective x := by
    have h := (f ≫ g).stalkMap_surjective x
    rw [Scheme.Hom.stalkMap_comp] at h
    exact Function.Surjective.of_comp h

theorem comp_iff {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsPreimmersion g] :
    IsPreimmersion (f ≫ g) ↔ IsPreimmersion f :=
  ⟨fun _ ↦ of_comp f g, fun _ ↦ inferInstance⟩

lemma SpecMap_iff {R S : CommRingCat.{u}} (f : R ⟶ S) :
    IsPreimmersion (Spec.map f) ↔ IsEmbedding (PrimeSpectrum.comap f.hom) ∧
      f.hom.SurjectiveOnStalks := by
  rw [← HasRingHomProperty.Spec_iff (P := @SurjectiveOnStalks), isPreimmersion_iff, and_comm]
  rfl

lemma mk_SpecMap {R S : CommRingCat.{u}} {f : R ⟶ S}
    (h₁ : IsEmbedding (PrimeSpectrum.comap f.hom)) (h₂ : f.hom.SurjectiveOnStalks) :
    IsPreimmersion (Spec.map f) :=
  (SpecMap_iff f).mpr ⟨h₁, h₂⟩

lemma of_isLocalization {R S : Type u} [CommRing R] (M : Submonoid R) [CommRing S]
    [Algebra R S] [IsLocalization M S] :
    IsPreimmersion (Spec.map (CommRingCat.ofHom <| algebraMap R S)) :=
  IsPreimmersion.mk_SpecMap
    (PrimeSpectrum.localization_comap_isEmbedding (R := R) S M)
    (RingHom.surjectiveOnStalks_of_isLocalization (M := M) S)

open Limits MorphismProperty in
instance : IsStableUnderBaseChange @IsPreimmersion := by
  refine .mk' fun X Y Z f g _ _ ↦ ?_
  have := pullback_fst (P := @SurjectiveOnStalks) f g inferInstance
  constructor
  let L (x : (pullback f g :)) : { x : X × Y | f x.1 = g x.2 } :=
    ⟨⟨pullback.fst f g x, pullback.snd f g x⟩,
    by simp only [Set.mem_setOf, ← Scheme.Hom.comp_apply, pullback.condition]⟩
  have : IsEmbedding L := IsEmbedding.of_comp (by fun_prop) continuous_subtype_val
    (SurjectiveOnStalks.isEmbedding_pullback f g)
  exact IsEmbedding.subtypeVal.comp ((TopCat.pullbackHomeoPreimage _ f.continuous _
    g.isEmbedding).isEmbedding.comp this)

variable {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z)

instance [IsPreimmersion g] : IsPreimmersion (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance [IsPreimmersion f] : IsPreimmersion (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [IsPreimmersion f] : IsPreimmersion (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

end IsPreimmersion

end AlgebraicGeometry

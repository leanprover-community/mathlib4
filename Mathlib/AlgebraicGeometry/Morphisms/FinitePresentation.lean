/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Spectrum.Prime.Chevalley

/-!

# Morphisms of finite presentation

A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y` and
`V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation.

A morphism of schemes is of finite presentation if it is both locally of finite presentation and
quasi-compact. We do not provide a separate declaration for this, instead simply assume both
conditions.

We show that these properties are local, and are stable under compositions.

-/


noncomputable section

open CategoryTheory Topology

universe v u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A morphism of schemes `f : X ⟶ Y` is locally of finite presentation if for each affine `U ⊆ Y`
and `V ⊆ f ⁻¹' U`, The induced map `Γ(Y, U) ⟶ Γ(X, V)` is of finite presentation. -/
@[mk_iff]
class LocallyOfFinitePresentation : Prop where
  finitePresentation_of_affine_subset :
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1),
      (f.appLE U V e).hom.FinitePresentation

instance : HasRingHomProperty @LocallyOfFinitePresentation RingHom.FinitePresentation where
  isLocal_ringHomProperty := RingHom.finitePresentation_isLocal
  eq_affineLocally' := by
    ext X Y f
    rw [locallyOfFinitePresentation_iff, affineLocally_iff_affineOpens_le]

instance (priority := 900) locallyOfFinitePresentation_of_isOpenImmersion [IsOpenImmersion f] :
    LocallyOfFinitePresentation f :=
  HasRingHomProperty.of_isOpenImmersion
    RingHom.finitePresentation_holdsForLocalizationAway.containsIdentities

instance : MorphismProperty.IsStableUnderComposition @LocallyOfFinitePresentation :=
  HasRingHomProperty.stableUnderComposition RingHom.finitePresentation_stableUnderComposition

instance locallyOfFinitePresentation_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [hf : LocallyOfFinitePresentation f] [hg : LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (f ≫ g) :=
  MorphismProperty.comp_mem _ f g hf hg

instance locallyOfFinitePresentation_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @LocallyOfFinitePresentation :=
  HasRingHomProperty.isStableUnderBaseChange RingHom.finitePresentation_isStableUnderBaseChange

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst _ _ inferInstance

instance {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) [LocallyOfFinitePresentation f] :
    LocallyOfFinitePresentation (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd _ _ inferInstance

instance {X Y : Scheme.{u}} (f : X ⟶ Y) [hf : LocallyOfFinitePresentation f] :
    LocallyOfFiniteType f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation] at hf
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFiniteType]
  refine affineLocally_le (fun hf ↦ ?_) f hf
  exact RingHom.FiniteType.of_finitePresentation hf

/-- **Chevalley's Theorem**: The image of a locally constructible set under a
morphism of finite presentation is locally constructible. -/
@[stacks 054K]
-- `nonrec` is needed for `wlog`
nonrec lemma Scheme.Hom.isLocallyConstructible_image (f : X.Hom Y)
    [hf : LocallyOfFinitePresentation f] [QuasiCompact f]
    {s : Set X} (hs : IsLocallyConstructible s) :
    IsLocallyConstructible (f.base '' s) := by
  wlog hY : ∃ R, Y = Spec R
  · refine .of_isOpenCover Y.affineCover.isOpenCover_opensRange fun i ↦ ?_
    have inst : LocallyOfFinitePresentation (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    have inst : QuasiCompact (Y.affineCover.pullbackHom f i) :=
      MorphismProperty.pullback_snd _ _ inferInstance
    convert (this (Y.affineCover.pullbackHom f i) (hs.preimage_of_isOpenEmbedding
      ((Y.affineCover.pullbackCover f).map i).isOpenEmbedding)
      ⟨_, rfl⟩).preimage_of_isOpenEmbedding (Y.affineCover.map i).isoOpensRange.inv.isOpenEmbedding
    refine .trans ?_ ((Scheme.homeoOfIso (Y.affineCover.map i).isoOpensRange).image_eq_preimage _)
    apply Set.image_injective.mpr Subtype.val_injective
    rw [Set.image_preimage_eq_inter_range, ← Set.image_comp, ← Set.image_comp,
      Subtype.range_coe_subtype, Set.setOf_mem_eq]
    change _ = (Y.affineCover.pullbackHom f i ≫
      (Y.affineCover.map i).isoOpensRange.hom ≫ Opens.ι _).base.hom '' _
    rw [Scheme.Hom.isoOpensRange_hom_ι, Cover.pullbackHom_map, Scheme.comp_base, TopCat.hom_comp,
      ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range]
    simp only [coe_opensRange, Cover.pullbackCover_obj, Cover.pullbackCover_map,
      IsOpenImmersion.range_pullback_fst_of_right, TopologicalSpace.Opens.map_obj,
      TopologicalSpace.Opens.carrier_eq_coe, TopologicalSpace.Opens.coe_mk,
      Set.image_inter_preimage]
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : CompactSpace X := HasAffineProperty.iff_of_isAffine.mp ‹QuasiCompact f›
    let 𝒰 := X.affineCover.finiteSubcover
    rw [← 𝒰.isOpenCover_opensRange.iUnion_inter s, Set.image_iUnion]
    refine .iUnion fun i ↦ ?_
    have inst : QuasiCompact (𝒰.map i ≫ f) :=
      HasAffineProperty.iff_of_isAffine.mpr (inferInstanceAs (CompactSpace (Spec _)))
    convert this (hs.preimage_of_isOpenEmbedding (𝒰.map i).isOpenEmbedding) _
      (𝒰.map i ≫ f) ⟨_, rfl⟩
    rw [Scheme.comp_base, ← TopCat.Hom.hom, ← TopCat.Hom.hom, TopCat.hom_comp,
      ContinuousMap.coe_comp, Set.image_comp, Set.image_preimage_eq_inter_range, coe_opensRange]
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)] at hf
  exact (PrimeSpectrum.isConstructible_comap_image hf hs.isConstructible).isLocallyConstructible

/-- **Chevalley's Theorem**: The image of a constructible set under a
morphism of finite presentation into a qcqs scheme is constructible. -/
@[stacks 054J]
lemma Scheme.Hom.isConstructible_image (f : X.Hom Y)
    [LocallyOfFinitePresentation f] [QuasiCompact f] [CompactSpace Y] [QuasiSeparatedSpace Y]
    {s : Set X} (hs : IsConstructible s) :
    IsConstructible (f.base '' s) :=
  (f.isLocallyConstructible_image hs.isLocallyConstructible).isConstructible

@[stacks 054I]
lemma Scheme.Hom.isConstructible_preimage (f : X.Hom Y) {s : Set Y} (hs : IsConstructible s) :
    IsConstructible (f.base ⁻¹' s) :=
  hs.preimage f.continuous fun t ht ht' ↦ IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr
    ((quasiCompact_iff_spectral _).mp
    (MorphismProperty.of_isPullback (P := @QuasiCompact)
    (isPullback_morphismRestrict f ⟨t, ht⟩)
    ((quasiCompact_iff_spectral _).mpr (IsRetrocompact_iff_isSpectralMap_subtypeVal.mp ht'))))

end AlgebraicGeometry

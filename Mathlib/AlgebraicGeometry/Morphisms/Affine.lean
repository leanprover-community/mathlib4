/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!

# Affine morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is affine if the preimage
of an arbitrary affine open subset of `Y` is affine.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine.

## Main results

- `AlgebraicGeometry.IsAffineHom`: The class of affine morphisms.
- `AlgebraicGeometry.isAffineOpen_of_isAffineOpen_basicOpen`:
  If `s` is a spanning set of `Γ(X, U)`, such that each `X.basicOpen i` is affine,
  then `U` is also affine.
- `AlgebraicGeometry.isAffineHom_isStableUnderBaseChange`:
  Affine morphisms are stable under base change.

We also provide the instance `HasAffineProperty @IsAffineHom fun X _ _ _ ↦ IsAffine X`.

-/

universe v u

open CategoryTheory Limits TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes `X ⟶ Y` is affine if
the preimage of any affine open subset of `Y` is affine. -/
@[mk_iff]
class IsAffineHom {X Y : Scheme} (f : X ⟶ Y) : Prop where
  isAffine_preimage : ∀ U : Y.Opens, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)

lemma IsAffineOpen.preimage {X Y : Scheme} {U : Y.Opens} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsAffineHom f] :
    IsAffineOpen (f ⁻¹ᵁ U) :=
  IsAffineHom.isAffine_preimage _ hU

@[deprecated (since := "2025-10-07")] alias affinePreimage := IsAffineOpen.preimage

instance (priority := 900) [IsIso f] : IsAffineHom f :=
  ⟨fun _ hU ↦ hU.preimage_of_isIso f⟩

instance (priority := 900) [IsAffineHom f] : QuasiCompact f :=
  quasiCompact_iff_forall_isAffineOpen.mpr fun _ hU ↦ (hU.preimage f).isCompact

instance [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  constructor
  intro U hU
  rw [Scheme.Hom.comp_base, Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

instance : MorphismProperty.IsMultiplicative @IsAffineHom where
  id_mem := inferInstance
  comp_mem _ _ _ _ := inferInstance

instance {X : Scheme} (r : Γ(X, ⊤)) :
    IsAffineHom (X.basicOpen r).ι := by
  constructor
  intro U hU
  fapply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (X.basicOpen r).ι).mp
  convert hU.basicOpen (X.presheaf.map (homOfLE le_top).op r)
  rw [X.basicOpen_res]
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  simp

lemma isRetrocompact_basicOpen (s : Γ(X, ⊤)) : IsRetrocompact (X := X) (X.basicOpen s) :=
  IsRetrocompact_iff_isSpectralMap_subtypeVal.mpr (X.basicOpen s).ι.isSpectralMap

/-- Superseded by `isAffine_of_isAffineOpen_basicOpen`. -/
private lemma isAffine_of_isAffineOpen_basicOpen_aux (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  rw [← Set.inter_univ (_ ∩ _), ← Opens.coe_top, ← iSup_basicOpen_of_span_eq_top _ _ e,
    ← iSup_subtype'', Opens.coe_iSup, Set.inter_iUnion]
  apply isCompact_iUnion
  intro i
  rw [Set.inter_inter_distrib_right]
  refine (hs₂ i (hs' i.2)).isQuasiSeparated _ _ Set.inter_subset_right
    (U.1.2.inter (X.basicOpen _).2) ?_ Set.inter_subset_right (V.1.2.inter (X.basicOpen _).2) ?_
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (U.2.basicOpen _).isCompact
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (V.2.basicOpen _).isCompact

@[stacks 01QF]
lemma isAffine_of_isAffineOpen_basicOpen (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    IsAffine X := by
  have : QuasiSeparatedSpace X := isAffine_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff, ← Opens.coe_top, ← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    apply s'.isCompact_biUnion
    exact fun i hi ↦ (hs₂ _ (hs' hi)).isCompact
  constructor
  refine HasAffineProperty.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i : s ↦ ⟨PrimeSpectrum.basicOpen i.1, ?_⟩) ?_ (fun i ↦ ⟨?_, ?_⟩)
  · change IsAffineOpen _
    simp only [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Scheme.Spec.obj (op _))).basicOpen _
  · rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Subtype.range_coe_subtype, Set.setOf_mem_eq, hs]
  · rw [Scheme.toSpecΓ_preimage_basicOpen]
    exact hs₂ _ i.2
  · simp only [Opens.map_top, morphismRestrict_app]
    refine IsIso.comp_isIso' ?_ inferInstance
    convert isIso_ΓSpec_adjunction_unit_app_basicOpen i.1 using 0
    exact congr(IsIso ((ΓSpec.adjunction.unit.app X).app $(by simp)))

/--
If `s` is a spanning set of `Γ(X, U)`, such that each `X.basicOpen i` is affine, then `U` is also
affine.
-/
lemma isAffineOpen_of_isAffineOpen_basicOpen (U) (s : Set Γ(X, U))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    IsAffineOpen U := by
  apply isAffine_of_isAffineOpen_basicOpen (U.topIso.inv '' s)
  · rw [← Ideal.map_span U.topIso.inv.hom, hs, Ideal.map_top]
  · rintro _ ⟨j, hj, rfl⟩
    rw [← (Scheme.Opens.ι _).isAffineOpen_iff_of_isOpenImmersion, Scheme.image_basicOpen]
    simpa [Scheme.Opens.toScheme_presheaf_obj] using hs₂ j hj

instance : HasAffineProperty @IsAffineHom fun X _ _ _ ↦ IsAffine X where
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : IsAffine _ := H
        exact .of_isIso e.hom
      · exact fun _ _ _ ↦ id
    · intro X Y _ f r H
      have : IsAffine X := H
      change IsAffineOpen _
      rw [Scheme.preimage_basicOpen]
      exact (isAffineOpen_top X).basicOpen _
    · intro X Y _ f S hS hS'
      apply_fun Ideal.map (f.appTop).hom at hS
      rw [Ideal.map_span, Ideal.map_top] at hS
      apply isAffine_of_isAffineOpen_basicOpen _ hS
      have : ∀ i : S, IsAffineOpen (f⁻¹ᵁ Y.basicOpen i.1) := hS'
      simpa [Scheme.preimage_basicOpen] using this
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [targetAffineLocally, Scheme.affineOpens, Set.coe_setOf, Set.mem_setOf_eq,
      Subtype.forall, isAffineHom_iff]
    rfl

instance isAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @IsAffineHom := by
  apply HasAffineProperty.isStableUnderBaseChange
  letI := HasAffineProperty.isLocal_affineProperty
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  introv X hX H
  infer_instance

instance (priority := 100) isAffineHom_of_isAffine [IsAffine X] [IsAffine Y] : IsAffineHom f :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom)).mpr inferInstance

lemma isAffine_of_isAffineHom [IsAffineHom f] [IsAffine Y] : IsAffine X :=
  (HasAffineProperty.iff_of_isAffine (P := @IsAffineHom) (f := f)).mp inferInstance

lemma isAffineHom_of_forall_exists_isAffineOpen
    (H : ∀ x : Y, ∃ U : Y.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsAffineOpen (f ⁻¹ᵁ U)) :
    IsAffineHom f := by
  choose U hxU hU hfU using H
  rw [HasAffineProperty.iff_of_iSup_eq_top (P := @IsAffineHom) fun i ↦ ⟨U i, hU i⟩]
  · exact hfU
  · exact top_le_iff.mp (fun x _ ↦ by simpa using ⟨x, hxU x⟩)

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom f] [IsAffine Y] :
    IsAffine (pullback f g) :=
  letI : IsAffineHom (pullback.snd f g) := MorphismProperty.pullback_snd _ _ ‹_›
  isAffine_of_isAffineHom (pullback.snd f g)

instance {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffineHom g] [IsAffine X] :
    IsAffine (pullback f g) :=
  letI : IsAffineHom (pullback.fst f g) := MorphismProperty.pullback_fst _ _ ‹_›
  isAffine_of_isAffineHom (pullback.fst f g)

/-- If the underlying map of a morphism is inducing and has closed range, then it is affine. -/
@[stacks 04DE]
lemma isAffineHom_of_isInducing
    (hf₁ : Topology.IsInducing f.base)
    (hf₂ : IsClosed (Set.range f.base)) :
    IsAffineHom f := by
  apply isAffineHom_of_forall_exists_isAffineOpen
  intro y
  by_cases hy : y ∈ Set.range f.base
  · obtain ⟨x, rfl⟩ := hy
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
    obtain ⟨U', hU'U, rfl⟩ : ∃ U' : Y.Opens, U' ≤ U ∧ f ⁻¹ᵁ U' = V := by
      obtain ⟨U', hU', e⟩ := hf₁.isOpen_iff.mp V.2
      exact ⟨⟨U', hU'⟩ ⊓ U, inf_le_right, Opens.ext (by simpa [e] using hVU)⟩
    obtain ⟨r, hrU', hxr⟩ := hU.exists_basicOpen_le ⟨f.base x, hxV⟩ hxU
    refine ⟨_, hxr, hU.basicOpen r, ?_⟩
    convert hV.basicOpen (f.app _ (Y.presheaf.map (homOfLE hU'U).op r)) using 1
    simp only [Scheme.preimage_basicOpen, ← CommRingCat.comp_apply, f.naturality]
    simpa using ((Opens.map f.base).map (homOfLE hrU')).le
  · obtain ⟨_, ⟨U, hU, rfl⟩, hyU, hU'⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy hf₂.isOpen_compl
    rw [Set.subset_compl_iff_disjoint_right, ← Set.preimage_eq_empty_iff] at hU'
    refine ⟨U, hyU, hU, ?_⟩
    convert isAffineOpen_bot _
    exact Opens.ext hU'

end AlgebraicGeometry

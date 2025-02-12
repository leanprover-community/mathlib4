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

## TODO
- Affine morphisms are separated.

-/

universe v u

open CategoryTheory TopologicalSpace Opposite

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

/-- The preimage of an affine open as an `Scheme.affine_opens`. -/
@[simps]
def affinePreimage {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] (U : Y.affineOpens) :
    X.affineOpens :=
  ⟨f ⁻¹ᵁ U.1, IsAffineHom.isAffine_preimage _ U.prop⟩

instance (priority := 900) [IsIso f] : IsAffineHom f :=
  ⟨fun _ hU ↦ hU.preimage_of_isIso f⟩

instance (priority := 900) [IsAffineHom f] : QuasiCompact f :=
  (quasiCompact_iff_forall_affine f).mpr
    (fun U hU ↦ (IsAffineHom.isAffine_preimage U hU).isCompact)

instance [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  constructor
  intros U hU
  rw [Scheme.comp_base, Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

instance : MorphismProperty.IsMultiplicative @IsAffineHom where
  id_mem := inferInstance
  comp_mem _ _ _ _ := inferInstance

instance {X : Scheme} (r : Γ(X, ⊤)) :
    IsAffineHom (X.basicOpen r).ι := by
  constructor
  intros U hU
  fapply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (X.basicOpen r).ι).mp
  convert hU.basicOpen (X.presheaf.map (homOfLE le_top).op r)
  rw [X.basicOpen_res]
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  simp

lemma isAffineOpen_of_isAffineOpen_basicOpen_aux (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_affine]
  intros U V
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

lemma isAffine_of_isAffineOpen_basicOpen (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    IsAffine X := by
  have : QuasiSeparatedSpace X := isAffineOpen_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff, ← Opens.coe_top, ← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    apply s'.isCompact_biUnion
    exact fun i hi ↦ (hs₂ _ (hs' hi)).isCompact
  constructor
  refine HasAffineProperty.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun i : s ↦ ⟨PrimeSpectrum.basicOpen i.1, ?_⟩) ?_ (fun i ↦ ⟨?_, ?_⟩)
  · show IsAffineOpen _
    simp only [← basicOpen_eq_of_affine]
    exact (isAffineOpen_top (Scheme.Spec.obj (op _))).basicOpen _
  · rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Subtype.range_coe_subtype, Set.setOf_mem_eq, hs]
  · rw [Scheme.toSpecΓ_preimage_basicOpen]
    exact hs₂ _ i.2
  · simp only [Functor.comp_obj, Functor.rightOp_obj, Scheme.Γ_obj, Scheme.Spec_obj, id_eq,
      eq_mpr_eq_cast, Functor.id_obj, Opens.map_top, morphismRestrict_app]
    refine IsIso.comp_isIso' ?_ inferInstance
    convert isIso_ΓSpec_adjunction_unit_app_basicOpen i.1 using 0
    refine congr(IsIso ((ΓSpec.adjunction.unit.app X).app $(?_)))
    rw [Opens.isOpenEmbedding_obj_top]

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
        exact isAffine_of_isIso e.hom
      · exact fun _ _ _ ↦ id
    · intro X Y _ f r H
      have : IsAffine X := H
      show IsAffineOpen _
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

end AlgebraicGeometry

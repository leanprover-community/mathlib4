/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.LocalProperties

#align_import algebraic_geometry.morphisms.ring_hom_properties from "leanprover-community/mathlib"@"d39590fc8728fbf6743249802486f8c91ffe07bc"

/-!

# Properties of morphisms from properties of ring homs.

We provide the basic framework for talking about properties of morphisms that come from properties
of ring homs. For `P` a property of ring homs, we have two ways of defining a property of scheme
morphisms:

Let `f : X ⟶ Y`,
- `targetAffineLocally (affine_and P)`: the preimage of an affine open `U = Spec A` is affine
  (`= Spec B`) and `A ⟶ B` satisfies `P`. (TODO)
- `affineLocally P`: For each pair of affine open `U = Spec A ⊆ X` and `V = Spec B ⊆ f ⁻¹' U`,
  the ring hom `A ⟶ B` satisfies `P`.

For these notions to be well defined, we require `P` be a sufficient local property. For the former,
`P` should be local on the source (`RingHom.RespectsIso P`, `RingHom.LocalizationPreserves P`,
`RingHom.OfLocalizationSpan`), and `targetAffineLocally (affine_and P)` will be local on
the target. (TODO)

For the latter `P` should be local on the target (`RingHom.PropertyIsLocal P`), and
`affineLocally P` will be local on both the source and the target.

Further more, these properties are stable under compositions (resp. base change) if `P` is. (TODO)

-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

namespace RingHom

theorem StableUnderBaseChange.Γ_pullback_fst (hP : StableUnderBaseChange @P) (hP' : RespectsIso @P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P (Scheme.Γ.map g.op)) : P (Scheme.Γ.map (pullback.fst f g).op) := by
  -- Porting note (#11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [op_comp, Functor.map_comp, hP'.cancel_right_isIso, AffineScheme.forgetToScheme_map]
  have :=
    _root_.congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.rightOp (AffineScheme.ofHom f)
        (AffineScheme.ofHom g))
  simp only [Quiver.Hom.unop_op, Functor.rightOp_map, unop_comp] at this
  delta AffineScheme.Γ at this
  simp only [Quiver.Hom.unop_op, Functor.comp_map, AffineScheme.forgetToScheme_map,
    Functor.op_map] at this
  rw [← this, hP'.cancel_right_isIso, ← pushoutIsoUnopPullback_inl_hom, hP'.cancel_right_isIso]
  exact hP.pushout_inl _ hP' _ _ H
#align ring_hom.stable_under_base_change.Γ_pullback_fst RingHom.StableUnderBaseChange.Γ_pullback_fst

end RingHom

namespace AlgebraicGeometry

/-- For `P` a property of ring homomorphisms, `sourceAffineLocally P` holds for `f : X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`. -/
def sourceAffineLocally : AffineTargetMorphismProperty := fun X _ f _ =>
  ∀ U : X.affineOpens, P (Scheme.Γ.map (Scheme.ιOpens U ≫ f).op)
#align algebraic_geometry.source_affine_locally AlgebraicGeometry.sourceAffineLocally

variable {P}

theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso @P) :
    (sourceAffineLocally @P).toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    rw [← h₁.cancel_right_isIso _ (Scheme.Γ.map (Scheme.restrictMapIso e.inv U.1).hom.op), ←
      Functor.map_comp, ← op_comp]
    convert H ⟨_, U.prop.preimage_of_isIso e.inv⟩ using 3
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Category.assoc,
      e.inv_hom_id_assoc]
  · introv H U
    rw [← Category.assoc, op_comp, Functor.map_comp, h₁.cancel_left_isIso]
    exact H U
#align algebraic_geometry.source_affine_locally_respects_iso AlgebraicGeometry.sourceAffineLocally_respectsIso

open Scheme in
theorem Γ_ιOpens_comp_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (V) :
    P (Γ.map (ιOpens V ≫ f).op) ↔ P (f.appLE ⊤ V le_top) := by
  simp only [Γ_obj, restrict_presheaf_obj, op_comp, Γ_map, unop_comp, Quiver.Hom.unop_op, comp_app,
    Opens.map_top, ofRestrict_val_base, ofRestrict_app, TopCat.coe_of, Functor.id_obj,
    Opens.coe_inclusion, Functor.comp_obj, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map,
    comp_appLE, Opens.map_top, restrict_presheaf_obj, ofRestrict_appLE]
  exact f.appLE_congr _ rfl V.openEmbedding_obj_top _

open Scheme in
theorem Γ_ιOpens_morphismRestrict_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (U V) :
    P (Γ.map (ιOpens V ≫ f ∣_ U).op) ↔ P (f.appLE U (ιOpens _ ''ᵁ V)
      ((Set.image_subset_range _ _).trans Subtype.range_val.subset)) := by
  simp only [Γ_obj, restrict_presheaf_obj, op_comp, Γ_map, unop_comp, Quiver.Hom.unop_op, comp_app,
    Opens.map_top, ofRestrict_val_base, morphismRestrict_app', ofRestrict_app, TopCat.coe_of,
    Functor.id_obj, Opens.coe_inclusion, Functor.comp_obj, restrict_presheaf_map, Hom.appLE_map]
  apply f.appLE_congr
  · exact U.openEmbedding_obj_top
  · rw [Opens.openEmbedding_obj_top]

open Scheme in
theorem sourceAffineLocally_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Opens Y) (hU : IsAffineOpen U) :
    @sourceAffineLocally P _ _ (f ∣_ U) hU ↔
      ∀ (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U), P (f.appLE U V e) := by
  dsimp only [sourceAffineLocally]
  conv_lhs => intro V; rw [Γ_ιOpens_morphismRestrict_iff (P := P) f U V]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun V h ↦ ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  apply f.appLE_congr _ rfl congr(Subtype.val <| Subtype.val $(this))

theorem sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso @P)
    (h₂ : RingHom.LocalizationPreserves @P) (h₃ : RingHom.OfLocalizationSpan @P) :
    (sourceAffineLocally @P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso h₁
  · intro X Y _ f r H
    rw [sourceAffineLocally_morphismRestrict]
    intro U hU
    have : X.basicOpen (f.appLE ⊤ U (by simp) r) = U := by
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.coe_comp_of, RingHom.coe_comp,
        Function.comp_apply]
      rw [Scheme.basicOpen_res]
      simpa using hU
    rw [← f.appLE_congr _ rfl this P,
      IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2 _ r]
    apply (config := { allowSynthFailures := true }) h₂.away
    exact (f.appLE_congr _ rfl U.1.openEmbedding_obj_top P).mp (by simpa using H U)
  · introv hs hs' U
    apply h₃ _ _ hs
    intro r
    have : IsAffineOpen (X.basicOpen (f.appLE ⊤ (Scheme.ιOpens U ''ᵁ ⊤) le_top r.1)) := by
      convert U.2.basicOpen (f.appLE ⊤ U le_top r.1) using 1
      simp only [Scheme.Hom.appLE, Opens.map_top, CommRingCat.coe_comp_of, RingHom.coe_comp,
        Function.comp_apply]
      rw [Scheme.basicOpen_res, Scheme.basicOpen_res]
      congr 1
      exact Opens.openEmbedding_obj_top _
    simp_rw [sourceAffineLocally_morphismRestrict] at hs'
    have := hs' r ⟨X.basicOpen (f.appLE ⊤ (Scheme.ιOpens U ''ᵁ ⊤) le_top r.1), this⟩
        (by simpa [Scheme.Hom.appLE] using Scheme.basicOpen_restrict _ _ _)
    simp only at this
    rwa [IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y)
      (by rw [U.1.openEmbedding_obj_top]; exact U.2), ← h₁.is_localization_away_iff] at this
#align algebraic_geometry.source_affine_locally_is_local AlgebraicGeometry.sourceAffineLocally_isLocal

variable (P)

/-- For `P` a property of ring homomorphisms, `affineLocally P` holds for `f : X ⟶ Y` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.
Also see `affineLocally_iff_affineOpens_le`. -/
abbrev affineLocally : MorphismProperty Scheme.{u} :=
  targetAffineLocally (sourceAffineLocally @P)
#align algebraic_geometry.affine_locally AlgebraicGeometry.affineLocally

theorem affineLocally_respectsIso (h : RingHom.RespectsIso @P) : (affineLocally @P).RespectsIso :=
  letI := sourceAffineLocally_respectsIso h
  inferInstance
#align algebraic_geometry.affine_locally_respects_iso AlgebraicGeometry.affineLocally_respectsIso

open Scheme in
theorem affineLocally_iff_affineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} (@P) f ↔
      ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), P (f.appLE U V e) := by
  apply forall_congr'
  intro U
  exact sourceAffineLocally_morphismRestrict f U U.2
#align algebraic_geometry.affine_locally_iff_affine_opens_le AlgebraicGeometry.affineLocally_iff_affineOpens_le

variable (hP : RingHom.PropertyIsLocal @P)

theorem isOpenImmersion_comp_of_sourceAffineLocally (h₁ : RingHom.RespectsIso @P)
    {X Y Z : Scheme.{u}} [IsAffine X] [IsAffine Z] (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z)
    (h₂ : sourceAffineLocally (@P) g) : P (Scheme.Γ.map (f ≫ g).op) := by
  rw [← h₁.cancel_right_isIso _
    (Scheme.Γ.map (IsOpenImmersion.isoOfRangeEq (Y.ofRestrict _) f _).hom.op),
    ← Functor.map_comp, ← op_comp]
  · convert h₂ ⟨_, isAffineOpen_opensRange f⟩ using 3
    · rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
      exact Subtype.range_coe
#align algebraic_geometry.is_open_immersion_comp_of_source_affine_locally AlgebraicGeometry.isOpenImmersion_comp_of_sourceAffineLocally

end AlgebraicGeometry

open AlgebraicGeometry

namespace RingHom.PropertyIsLocal

variable {P} (hP : RingHom.PropertyIsLocal @P)

theorem sourceAffineLocally_of_source_openCover {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.obj i)] (H : ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :
    sourceAffineLocally (@P) f := by
  intro U
  let S i : X.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.map i)⟩
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r H =>
    rw [Γ_ιOpens_comp_iff (P := P)] at H ⊢
    rw [Scheme.affineBasicOpen_coe, ← f.appLE_map (U := ⊤) le_top (homOfLE (X.basicOpen_le r)).op]
    apply hP.StableUnderComposition _ _ H
    have := U.2.isLocalization_basicOpen r
    apply hP.HoldsForLocalizationAway _ r
  | openCover U s hs H =>
    simp only [Γ_ιOpens_comp_iff (P := P)] at H ⊢
    apply hP.OfLocalizationSpanTarget.ofIsLocalization hP.respectsIso _ _ hs
    rintro r
    refine ⟨_, _, _, IsAffineOpen.isLocalization_basicOpen U.2 r, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_eq_ring_hom_comp, Scheme.Hom.appLE_map]
    exact H r
  | hU i =>
    specialize H i
    rw [← hP.respectsIso.cancel_right_isIso _
        (Scheme.Γ.map
          (IsOpenImmersion.isoOfRangeEq (𝒰.map i) (X.ofRestrict (S i).1.openEmbedding)
                Subtype.range_coe.symm).inv.op)] at H
    rwa [← Scheme.Γ.map_comp, ← op_comp, IsOpenImmersion.isoOfRangeEq_inv_fac_assoc] at H
#align ring_hom.property_is_local.source_affine_locally_of_source_open_cover RingHom.PropertyIsLocal.sourceAffineLocally_of_source_openCover

theorem affine_openCover_TFAE {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE
      [sourceAffineLocally (@P) f,
        ∃ (𝒰 : Scheme.OpenCover.{u} X) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, P (Scheme.Γ.map (𝒰.map i ≫ f).op),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          P (Scheme.Γ.map (𝒰.map i ≫ f).op),
        ∀ {U : Scheme} (g : U ⟶ X) [IsAffine U] [IsOpenImmersion g],
          P (Scheme.Γ.map (g ≫ f).op)] := by
  tfae_have 1 → 4
  · intro H U g _ hg
    specialize H ⟨⟨_, hg.base_open.isOpen_range⟩, isAffineOpen_opensRange g⟩
    rw [← hP.respectsIso.cancel_right_isIso _ (Scheme.Γ.map (IsOpenImmersion.isoOfRangeEq g
      (X.ofRestrict (Opens.openEmbedding ⟨_, hg.base_open.isOpen_range⟩))
      Subtype.range_coe.symm).hom.op),
      ← Scheme.Γ.map_comp, ← op_comp, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc] at H
    exact H
  tfae_have 4 → 3
  · intro H 𝒰 _ i; apply H
  tfae_have 3 → 2
  · intro H; exact ⟨X.affineCover, inferInstance, H _⟩
  tfae_have 2 → 1
  · rintro ⟨𝒰, _, h𝒰⟩
    exact sourceAffineLocally_of_source_openCover hP f 𝒰 h𝒰
  tfae_finish
#align ring_hom.property_is_local.affine_open_cover_tfae RingHom.PropertyIsLocal.affine_openCover_TFAE

theorem openCover_TFAE {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE
      [sourceAffineLocally (@P) f,
        ∃ 𝒰 : Scheme.OpenCover.{u} X, ∀ i : 𝒰.J, sourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) (i : 𝒰.J), sourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ {U : Scheme} (g : U ⟶ X) [IsOpenImmersion g], sourceAffineLocally (@P) (g ≫ f)] := by
  tfae_have 1 → 4
  · intro H U g hg V
    -- Porting note: this has metavariable if I put it directly into rw
    have := (hP.affine_openCover_TFAE f).out 0 3
    rw [this] at H
    haveI : IsAffine _ := V.2
    rw [← Category.assoc]
    -- Porting note: Lean could find this previously
    have : IsOpenImmersion <| (Scheme.ofRestrict U (Opens.openEmbedding V.val)) ≫ g :=
      LocallyRingedSpace.IsOpenImmersion.comp _ _
    apply H
  tfae_have 4 → 3
  · intro H 𝒰 _ i; apply H
  tfae_have 3 → 2
  · intro H; exact ⟨X.affineCover, H _⟩
  tfae_have 2 → 1
  · rintro ⟨𝒰, h𝒰⟩
    -- Porting note: this has metavariable if I put it directly into rw
    have := (hP.affine_openCover_TFAE f).out 0 1
    rw [this]
    refine ⟨𝒰.bind fun _ => Scheme.affineCover _, ?_, ?_⟩
    · intro i; dsimp; infer_instance
    · intro i
      specialize h𝒰 i.1
      -- Porting note: this has metavariable if I put it directly into rw
      have := (hP.affine_openCover_TFAE (𝒰.map i.fst ≫ f)).out 0 3
      rw [this] at h𝒰
      -- Porting note: this was discharged after the apply previously
      have : IsAffine (Scheme.OpenCover.obj
        (Scheme.OpenCover.bind 𝒰 fun x ↦ Scheme.affineCover (Scheme.OpenCover.obj 𝒰 x)) i) := by
          dsimp; infer_instance
      apply @h𝒰 _ (show _ from _)
  tfae_finish
#align ring_hom.property_is_local.open_cover_tfae RingHom.PropertyIsLocal.openCover_TFAE

theorem sourceAffineLocally_comp_of_isOpenImmersion {X Y Z : Scheme.{u}} [IsAffine Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) [IsOpenImmersion f] (H : sourceAffineLocally (@P) g) :
    sourceAffineLocally (@P) (f ≫ g) := by
      -- Porting note: more tfae mis-behavior
      have := (hP.openCover_TFAE g).out 0 3
      apply this.mp H
#align ring_hom.property_is_local.source_affine_locally_comp_of_is_open_immersion RingHom.PropertyIsLocal.sourceAffineLocally_comp_of_isOpenImmersion

theorem source_affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y]
    (𝒰 : Scheme.OpenCover.{u} X) [∀ i, IsAffine (𝒰.obj i)] :
    sourceAffineLocally (@P) f ↔ ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op) := by
  -- Porting note: seems like TFAE is misbehaving; this used to be pure term proof but
  -- had strange failures where the output of TFAE turned into a metavariable when used despite
  -- being correctly displayed in the infoview
  refine ⟨fun H => ?_, fun H => ?_⟩
  · have h := (hP.affine_openCover_TFAE f).out 0 2
    apply h.mp
    exact H
  · have h := (hP.affine_openCover_TFAE f).out 1 0
    apply h.mp
    use 𝒰
#align ring_hom.property_is_local.source_affine_open_cover_iff RingHom.PropertyIsLocal.source_affine_openCover_iff

theorem isLocal_sourceAffineLocally : (sourceAffineLocally @P).IsLocal :=
  sourceAffineLocally_isLocal hP.respectsIso hP.LocalizationPreserves
    (@RingHom.PropertyIsLocal.ofLocalizationSpan _ hP)
#align ring_hom.property_is_local.is_local_source_affine_locally RingHom.PropertyIsLocal.isLocal_sourceAffineLocally

theorem hasAffinePropertyAffineLocally :
    HasAffineProperty (affineLocally @P) (sourceAffineLocally @P) where
  isLocal_affineProperty := hP.isLocal_sourceAffineLocally
  eq_targetAffineLocally' := rfl

theorem affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i))
    [∀ i j, IsAffine ((𝒰' i).obj j)] :
    affineLocally (@P) f ↔ ∀ i j, P (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd _ _).op) :=
  letI := hP.hasAffinePropertyAffineLocally
  (HasAffineProperty.iff_of_openCover 𝒰).trans
    (forall_congr' fun i => hP.source_affine_openCover_iff _ (𝒰' i))
#align ring_hom.property_is_local.affine_open_cover_iff RingHom.PropertyIsLocal.affine_openCover_iff

theorem source_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} X) :
    affineLocally (@P) f ↔ ∀ i, affineLocally (@P) (𝒰.map i ≫ f) := by
  constructor
  · intro H i U
    rw [morphismRestrict_comp]
    apply hP.sourceAffineLocally_comp_of_isOpenImmersion
    apply H
  · intro H U
    haveI : IsAffine _ := U.2
    apply ((hP.openCover_TFAE (f ∣_ U.1)).out 1 0).mp
    use 𝒰.pullbackCover (X.ofRestrict _)
    intro i
    specialize H i U
    rw [morphismRestrict_comp] at H
    delta morphismRestrict at H
    have := sourceAffineLocally_respectsIso hP.respectsIso
    rw [Category.assoc, (sourceAffineLocally P).cancel_left_of_respectsIso,
      ← (sourceAffineLocally P).cancel_left_of_respectsIso (pullbackSymmetry _ _).hom,
      pullbackSymmetry_hom_comp_snd_assoc] at H
    exact H
#align ring_hom.property_is_local.source_open_cover_iff RingHom.PropertyIsLocal.source_openCover_iff

theorem affineLocally_of_isOpenImmersion (hP : RingHom.PropertyIsLocal @P) {X Y : Scheme.{u}}
    (f : X ⟶ Y) [hf : IsOpenImmersion f] : affineLocally (@P) f := by
  intro U
  haveI H : IsAffine _ := U.2
  rw [← Category.comp_id (f ∣_ U)]
  apply hP.sourceAffineLocally_comp_of_isOpenImmersion
  -- Porting note: need to excuse Lean from synthesizing an instance
  rw [@source_affine_openCover_iff _ hP _ _ _ _ (Scheme.openCoverOfIsIso (𝟙 _)) (_)]
  · intro i
    let esto := Scheme.Γ.obj (Opposite.op (Y.restrict <| Opens.openEmbedding U.val))
    let eso := Scheme.Γ.obj (Opposite.op ((Scheme.openCoverOfIsIso
      (𝟙 (Y.restrict <| Opens.openEmbedding U.val))).obj i))
    have := hP.HoldsForLocalizationAway
    convert @this esto eso _ _ ?_ 1 ?_
    · exact (RingHom.algebraMap_toAlgebra (Scheme.Γ.map _)).symm
    · exact
        @IsLocalization.away_of_isUnit_of_bijective _ _ _ _ (_) _ isUnit_one Function.bijective_id
  · intro; exact H
#align ring_hom.property_is_local.affine_locally_of_is_open_immersion RingHom.PropertyIsLocal.affineLocally_of_isOpenImmersion

theorem affineLocally_of_comp
    (H : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (g : S →+* T), P (g.comp f) → P g)
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} (h : affineLocally (@P) (f ≫ g)) :
    affineLocally (@P) f := by
  let 𝒰 : ∀ i, ((Z.affineCover.pullbackCover (f ≫ g)).obj i).OpenCover := by
    intro i
    refine Scheme.OpenCover.bind ?_ fun i => Scheme.affineCover _
    apply Scheme.OpenCover.pushforwardIso _
      (pullbackRightPullbackFstIso g (Z.affineCover.map i) f).hom
    apply Scheme.Pullback.openCoverOfRight
    exact (pullback g (Z.affineCover.map i)).affineCover
  have h𝒰 : ∀ i j, IsAffine ((𝒰 i).obj j) := by dsimp [𝒰]; infer_instance
  let 𝒰' := (Z.affineCover.pullbackCover g).bind fun i => Scheme.affineCover _
  have h𝒰' : ∀ i, IsAffine (𝒰'.obj i) := by dsimp [𝒰']; infer_instance
  rw [hP.affine_openCover_iff f 𝒰' fun i => Scheme.affineCover _]
  rw [hP.affine_openCover_iff (f ≫ g) Z.affineCover 𝒰] at h
  rintro ⟨i, j⟩ k
  dsimp at i j k
  specialize h i ⟨j, k⟩
  dsimp only [𝒰, 𝒰', Scheme.OpenCover.bind_map, Scheme.OpenCover.pushforwardIso_obj,
    Scheme.Pullback.openCoverOfRight_obj, Scheme.OpenCover.pushforwardIso_map,
    Scheme.Pullback.openCoverOfRight_map, Scheme.OpenCover.bind_obj,
    Scheme.OpenCover.pullbackCover_obj, Scheme.OpenCover.pullbackCover_map] at h ⊢
  rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
    pullback.lift_snd_assoc, Category.assoc, ← Category.assoc, op_comp, Functor.map_comp] at h
  exact H _ _ h
#align ring_hom.property_is_local.affine_locally_of_comp RingHom.PropertyIsLocal.affineLocally_of_comp

theorem affineLocally_isStableUnderComposition : (affineLocally @P).IsStableUnderComposition where
  comp_mem {X Y S} f g hf hg := by
    let 𝒰 : ∀ i, ((S.affineCover.pullbackCover (f ≫ g)).obj i).OpenCover := by
      intro i
      refine Scheme.OpenCover.bind ?_ fun i => Scheme.affineCover _
      apply Scheme.OpenCover.pushforwardIso _
        (pullbackRightPullbackFstIso g (S.affineCover.map i) f).hom
      apply Scheme.Pullback.openCoverOfRight
      exact (pullback g (S.affineCover.map i)).affineCover
    haveI : ∀ i j, IsAffine ((𝒰 i).obj j) := by dsimp [𝒰]; infer_instance
    rw [hP.affine_openCover_iff (f ≫ g) S.affineCover 𝒰]
    rintro i ⟨j, k⟩
    dsimp at i j k
    dsimp only [𝒰, Scheme.OpenCover.bind_map, Scheme.OpenCover.pushforwardIso_obj,
      Scheme.Pullback.openCoverOfRight_obj, Scheme.OpenCover.pushforwardIso_map,
      Scheme.Pullback.openCoverOfRight_map, Scheme.OpenCover.bind_obj]
    rw [Category.assoc, Category.assoc, pullbackRightPullbackFstIso_hom_snd,
      pullback.lift_snd_assoc, Category.assoc, ← Category.assoc, op_comp, Functor.map_comp]
    apply hP.StableUnderComposition
    · -- Porting note: used to be exact _|>. hg i j but that can't find an instance
      apply hP.affine_openCover_iff _ _ _|>.mp
      exact hg
    · delta affineLocally at hf
      -- Porting note: again strange behavior of TFAE
      have := (hP.isLocal_sourceAffineLocally.affine_openCover_TFAE f).out 0 3
      rw [this] at hf
      -- Porting note: needed to help Lean with this instance (same as above)
      have : IsOpenImmersion <|
          ((pullback g (S.affineCover.map i)).affineCover.map j ≫ pullback.fst) :=
        LocallyRingedSpace.IsOpenImmersion.comp _ _
      specialize hf ((pullback g (S.affineCover.map i)).affineCover.map j ≫ pullback.fst)
      -- Porting note: again strange behavior of TFAE
      have := (hP.affine_openCover_TFAE
        (pullback.snd : pullback f ((pullback g (S.affineCover.map i)).affineCover.map j ≫
        pullback.fst) ⟶ _)).out 0 3
      rw [this] at hf
      apply hf
#align ring_hom.property_is_local.affine_locally_stable_under_composition RingHom.PropertyIsLocal.affineLocally_isStableUnderComposition

end RingHom.PropertyIsLocal

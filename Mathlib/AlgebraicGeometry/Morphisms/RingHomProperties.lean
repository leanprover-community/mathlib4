/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.LocalProperties

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
We also provide the following interface:

## `HasRingHomProperty`

`HasRingHomProperty P Q` is a type class asserting that `P` is local at the target and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q`.

For `HasRingHomProperty P Q` and `f : X ⟶ Y`, we provide these API lemmas:
- `AlgebraicGeometry.HasAffineProperty.iff_appLE`:
    `P f` if and only if `Q (f.appLE U V _)` for all affine `U : Opens Y` and `V : Opens X`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_openCover`:
    If `Y` is affine, `P f ↔ ∀ i, Q ((𝒰.map i ≫ f).app ⊤)` for an affine open cover `𝒰` of `X`.
- `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`:
    If `X` and `Y` are affine, then `P f ↔ Q (f.app ⊤)`.
- `AlgebraicGeometry.HasAffineProperty.Spec_iff`:
    `P (Spec.map φ) ↔ Q φ`
- `AlgebraicGeometry.HasAffineProperty.iff_of_iSup_eq_top`:
    If `Y` is affine, `P f ↔ ∀ i, Q (f.appLE ⊤ (U i) _)` for a family `U` of affine opens of `X`.
- `AlgebraicGeometry.HasAffineProperty.of_isOpenImmersion`:
    If `f` is an open immersion then `P f`.
- `AlgebraicGeometry.HasAffineProperty.stableUnderBaseChange`:
    If `Q` is stable under base change, then so is `P`.

We also provide the instances `P.IsMultiplicative`, `P.IsStableUnderComposition`,
`IsLocalAtTarget P`, `IsLocalAtSource P`.

-/

-- Explicit universe annotations were used in this file to improve perfomance #12737

universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

namespace RingHom

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

theorem StableUnderBaseChange.pullback_fst_app_top
    (hP : StableUnderBaseChange P) (hP' : RespectsIso P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P (g.app ⊤)) : P ((pullback.fst f g).app ⊤) := by
  -- Porting note (#11224): change `rw` to `erw`
  erw [← PreservesPullback.iso_inv_fst AffineScheme.forgetToScheme (AffineScheme.ofHom f)
      (AffineScheme.ofHom g)]
  rw [Scheme.comp_app, hP'.cancel_right_isIso, AffineScheme.forgetToScheme_map]
  have :=
    _root_.congr_arg Quiver.Hom.unop
      (PreservesPullback.iso_hom_fst AffineScheme.Γ.rightOp (AffineScheme.ofHom f)
        (AffineScheme.ofHom g))
  simp only [AffineScheme.Γ, Functor.rightOp_obj, Functor.comp_obj, Functor.op_obj, unop_comp,
    AffineScheme.forgetToScheme_obj, Scheme.Γ_obj, Functor.rightOp_map, Functor.comp_map,
    Functor.op_map, Quiver.Hom.unop_op, AffineScheme.forgetToScheme_map, Scheme.Γ_map] at this
  rw [← this, hP'.cancel_right_isIso, ← pushoutIsoUnopPullback_inl_hom, hP'.cancel_right_isIso]
  exact hP.pushout_inl _ hP' _ _ H

end RingHom

namespace AlgebraicGeometry

section affineLocally

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

/-- For `P` a property of ring homomorphisms, `sourceAffineLocally P` holds for `f : X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`. -/
def sourceAffineLocally : AffineTargetMorphismProperty := fun X _ f _ =>
  ∀ U : X.affineOpens, P (f.appLE ⊤ U le_top)

/-- For `P` a property of ring homomorphisms, `affineLocally P` holds for `f : X ⟶ Y` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.
Also see `affineLocally_iff_affineOpens_le`. -/
abbrev affineLocally : MorphismProperty Scheme.{u} :=
  targetAffineLocally (sourceAffineLocally P)

theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso P) :
    (sourceAffineLocally P).toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    have : IsIso (e.hom.appLE (e.hom ''ᵁ U) U.1 (e.hom.preimage_image_eq _).ge) :=
      inferInstanceAs (IsIso (e.hom.app _ ≫
        X.presheaf.map (eqToHom (e.hom.preimage_image_eq _).symm).op))
    rw [← Scheme.appLE_comp_appLE _ _ ⊤ (e.hom ''ᵁ U) U.1 le_top (e.hom.preimage_image_eq _).ge,
      h₁.cancel_right_isIso]
    exact H ⟨_, U.prop.image_of_isOpenImmersion e.hom⟩
  · introv H U
    rw [Scheme.comp_appLE, h₁.cancel_left_isIso]
    exact H U

theorem affineLocally_respectsIso (h : RingHom.RespectsIso P) : (affineLocally P).RespectsIso :=
  letI := sourceAffineLocally_respectsIso P h
  inferInstance

open Scheme in
theorem sourceAffineLocally_morphismRestrict {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U : Opens Y) (hU : IsAffineOpen U) :
    @sourceAffineLocally P _ _ (f ∣_ U) hU ↔
      ∀ (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U), P (f.appLE U V e) := by
  dsimp only [sourceAffineLocally]
  simp only [morphismRestrict_appLE]
  rw [(affineOpensRestrict (f ⁻¹ᵁ U)).forall_congr_left, Subtype.forall]
  refine forall₂_congr fun V h ↦ ?_
  have := (affineOpensRestrict (f ⁻¹ᵁ U)).apply_symm_apply ⟨V, h⟩
  exact f.appLE_congr _ (ιOpens_image_top _) congr($(this).1.1) _

theorem affineLocally_iff_affineOpens_le {X Y : Scheme.{u}} (f : X ⟶ Y) :
    affineLocally.{u} P f ↔
      ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1), P (f.appLE U V e) :=
  forall_congr' fun U ↦ sourceAffineLocally_morphismRestrict P f U U.2

theorem sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso P)
    (h₂ : RingHom.LocalizationPreserves P) (h₃ : RingHom.OfLocalizationSpan P) :
    (sourceAffineLocally P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso P h₁
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
    exact H U
  · introv hs hs' U
    apply h₃ _ _ hs
    intro r
    simp_rw [sourceAffineLocally_morphismRestrict] at hs'
    have := hs' r ⟨X.basicOpen (f.appLE ⊤ U le_top r.1), U.2.basicOpen (f.appLE ⊤ U le_top r.1)⟩
      (by simpa [Scheme.Hom.appLE] using Scheme.basicOpen_restrict _ _ _)
    rwa [IsAffineOpen.appLE_eq_away_map f (isAffineOpen_top Y) U.2,
      ← h₁.is_localization_away_iff] at this

end affineLocally

/--
`HasRingHomProperty P Q` is a type class asserting that `P` is local at the target and the source,
and for `f : Spec B ⟶ Spec A`, it is equivalent to the ring hom property `Q`.
To make the proofs easier, we state it instead as
1. `Q` is local (See `RingHom.PropertyIsLocal`)
2. `P f` if and only if `Q` holds for every `Γ(Y, U) ⟶ Γ(X, V)` for all affine `U`, `V`.
-/
class HasRingHomProperty (P : MorphismProperty Scheme.{u})
    (Q : outParam (∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)) : Prop where
  isLocal_ringHomProperty : RingHom.PropertyIsLocal Q
  eq_affineLocally' : P = affineLocally Q

namespace HasRingHomProperty

variable (P : MorphismProperty Scheme.{u}) {Q} [HasRingHomProperty P Q]
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma eq_affineLocally : P = affineLocally Q := eq_affineLocally'

instance : HasAffineProperty P (sourceAffineLocally Q) where
  isLocal_affineProperty := sourceAffineLocally_isLocal _
    (HasRingHomProperty.isLocal_ringHomProperty P).respectsIso
    (HasRingHomProperty.isLocal_ringHomProperty P).LocalizationPreserves
    (HasRingHomProperty.isLocal_ringHomProperty P).ofLocalizationSpan
  eq_targetAffineLocally' := eq_affineLocally P

theorem appLE (H : P f) (U : Y.affineOpens) (V : X.affineOpens) (e) : Q (f.appLE U V e) := by
  rw [eq_affineLocally P, affineLocally_iff_affineOpens_le] at H
  exact H _ _ _

theorem app_top (H : P f) [IsAffine X] [IsAffine Y] : Q (f.app ⊤) := by
  rw [Scheme.Hom.app_eq_appLE]
  exact appLE P f H ⟨_, isAffineOpen_top _⟩ ⟨_, isAffineOpen_top _⟩ _

theorem comp_of_isOpenImmersion [IsOpenImmersion f] (H : P g) :
    P (f ≫ g) := by
  rw [eq_affineLocally P, affineLocally_iff_affineOpens_le] at H ⊢
  intro U V e
  have : IsIso (f.appLE (f ''ᵁ V) V.1 (f.preimage_image_eq _).ge) :=
    inferInstanceAs (IsIso (f.app _ ≫
      X.presheaf.map (eqToHom (f.preimage_image_eq _).symm).op))
  rw [← Scheme.appLE_comp_appLE _ _ _ (f ''ᵁ V) V.1
    (Set.image_subset_iff.mpr e) (f.preimage_image_eq _).ge,
    (isLocal_ringHomProperty P).respectsIso.cancel_right_isIso]
  exact H _ ⟨_, V.2.image_of_isOpenImmersion _⟩ _

variable {P f}

lemma iff_appLE : P f ↔ ∀ (U : Y.affineOpens) (V : X.affineOpens) (e), Q (f.appLE U V e) := by
  rw [eq_affineLocally P, affineLocally_iff_affineOpens_le]

theorem of_openCover [IsAffine Y]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.obj i)] (H : ∀ i, Q ((𝒰.map i ≫ f).app ⊤)) :
    P f := by
  rw [HasAffineProperty.iff_of_isAffine (P := P)]
  intro U
  let S i : X.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.map i)⟩
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r H =>
    simp_rw [Scheme.affineBasicOpen_coe,
      ← f.appLE_map (U := ⊤) le_top (homOfLE (X.basicOpen_le r)).op]
    apply (isLocal_ringHomProperty P).StableUnderComposition _ _ H
    have := U.2.isLocalization_basicOpen r
    apply (isLocal_ringHomProperty P).HoldsForLocalizationAway _ r
  | openCover U s hs H =>
    apply (isLocal_ringHomProperty P).OfLocalizationSpanTarget.ofIsLocalization
      (isLocal_ringHomProperty P).respectsIso _ _ hs
    rintro r
    refine ⟨_, _, _, IsAffineOpen.isLocalization_basicOpen U.2 r, ?_⟩
    rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_eq_ring_hom_comp, Scheme.Hom.appLE_map]
    exact H r
  | hU i =>
    specialize H i
    rw [← (isLocal_ringHomProperty P).respectsIso.cancel_right_isIso _
      ((IsOpenImmersion.isoOfRangeEq (𝒰.map i) (Scheme.ιOpens (S i).1)
      Subtype.range_coe.symm).inv.app _), ← Scheme.comp_app,
      IsOpenImmersion.isoOfRangeEq_inv_fac_assoc, Scheme.comp_app,
      Scheme.ofRestrict_app, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map] at H
    exact (f.appLE_congr _ rfl (by simp) Q).mp H

theorem iff_of_openCover [IsAffine Y] (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.obj i)] :
    P f ↔ ∀ i, Q ((𝒰.map i ≫ f).app ⊤) :=
  ⟨fun H i ↦ app_top P _ (comp_of_isOpenImmersion P (𝒰.map i) f H), of_openCover 𝒰⟩

theorem iff_of_isAffine [IsAffine X] [IsAffine Y] :
    P f ↔ Q (f.app ⊤) := by
  rw [iff_of_openCover (P := P) (Scheme.openCoverOfIsIso.{u} (𝟙 _))]
  simp

theorem Spec_iff {R S : CommRingCat.{u}} {φ : R ⟶ S} :
    P (Spec.map φ) ↔ Q φ := by
  have H := (isLocal_ringHomProperty P).respectsIso
  rw [iff_of_isAffine (P := P), ← H.cancel_right_isIso _ (Scheme.ΓSpecIso _).hom,
    Scheme.ΓSpecIso_naturality, H.cancel_left_isIso]

theorem of_iSup_eq_top [IsAffine Y] {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤)
    (H : ∀ i, Q (f.appLE ⊤ (U i).1 le_top)) :
    P f := by
  have (i) : IsAffine ((X.openCoverOfSuprEqTop _ hU).obj i) := (U i).2
  refine of_openCover (X.openCoverOfSuprEqTop _ hU) fun i ↦ ?_
  simpa [Scheme.Hom.app_eq_appLE] using (f.appLE_congr _ rfl (by simp) Q).mp (H i)

theorem iff_of_iSup_eq_top [IsAffine Y] {ι : Type*}
    (U : ι → X.affineOpens) (hU : ⨆ i, (U i : Opens X) = ⊤) :
    P f ↔ ∀ i, Q (f.appLE ⊤ (U i).1 le_top) :=
  ⟨fun H _ ↦ appLE P f H ⟨_, isAffineOpen_top _⟩ _ le_top, of_iSup_eq_top U hU⟩

lemma HasAffineProperty.isLocalAtSource (P) {Q} [HasAffineProperty P Q]
    (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] (𝒰 : Scheme.OpenCover.{u} X),
        Q f ↔ ∀ i, Q (𝒰.map i ≫ f)) : IsLocalAtSource P where
  iff_of_openCover' {X Y} f 𝒰 := by
    simp_rw [IsLocalAtTarget.iff_of_iSup_eq_top _ (iSup_affineOpens_eq_top Y)]
    rw [forall_comm]
    refine forall_congr' fun U ↦ ?_
    simp_rw [HasAffineProperty.iff_of_isAffine, morphismRestrict_comp]
    exact @H _ _ (f ∣_ U.1) U.2 (𝒰.restrict (f ⁻¹ᵁ U.1))

instance : IsLocalAtSource P := by
  apply HasAffineProperty.isLocalAtSource
  intros X Y f _ 𝒰
  simp_rw [← HasAffineProperty.iff_of_isAffine (P := P),
    iff_of_openCover 𝒰.affineRefinement.openCover,
    fun i ↦ iff_of_openCover (P := P) (f := 𝒰.map i ≫ f) (𝒰.obj i).affineCover]
  simp [Scheme.OpenCover.affineRefinement]

instance : P.ContainsIdentities where
  id_mem X := by
    rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
    intro U
    rw [morphismRestrict_id, iff_of_isAffine (P := P), Scheme.id_app]
    have := IsLocalization.at_units (.powers (1 : Γ(X ∣_ᵤ 𝟙 X ⁻¹ᵁ U, ⊤))) (by simp)
    exact (isLocal_ringHomProperty P).HoldsForLocalizationAway Γ(X ∣_ᵤ 𝟙 X ⁻¹ᵁ U, ⊤) 1

instance : P.IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    wlog hZ : IsAffine Z generalizing X Y Z
    · rw [IsLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
      intro U
      rw [morphismRestrict_comp]
      exact this _ _ (IsLocalAtTarget.restrict hf _) (IsLocalAtTarget.restrict hg _) U.2
    wlog hY : IsAffine Y generalizing X Y
    · rw [IsLocalAtSource.iff_of_openCover (P := P) (Y.affineCover.pullbackCover f)]
      intro i
      rw [← Scheme.OpenCover.pullbackHom_map_assoc]
      exact this _ _ (IsLocalAtTarget.of_isPullback (.of_hasPullback _ _) hf)
        (comp_of_isOpenImmersion _ _ _ hg) inferInstance
    wlog hX : IsAffine X generalizing X
    · rw [IsLocalAtSource.iff_of_openCover (P := P) X.affineCover]
      intro i
      rw [← Category.assoc]
      exact this _ (comp_of_isOpenImmersion _ _ _ hf) inferInstance
    rw [iff_of_isAffine (P := P)] at hf hg ⊢
    exact (isLocal_ringHomProperty P).StableUnderComposition _ _ hg hf

instance : P.IsMultiplicative where

lemma of_isOpenImmersion [IsOpenImmersion f] : P f := IsLocalAtSource.of_isOpenImmersion f

lemma stableUnderBaseChange (hP : RingHom.StableUnderBaseChange Q) : P.StableUnderBaseChange := by
  apply HasAffineProperty.stableUnderBaseChange
  letI := HasAffineProperty.isLocal_affineProperty P
  apply AffineTargetMorphismProperty.StableUnderBaseChange.mk
  intros X Y S _ _ f g H
  rw [← HasAffineProperty.iff_of_isAffine (P := P)] at H ⊢
  wlog hX : IsAffine Y generalizing Y
  · rw [IsLocalAtSource.iff_of_openCover (P := P)
      (Scheme.Pullback.openCoverOfRight Y.affineCover f g)]
    intro i
    simp only [Scheme.Pullback.openCoverOfRight_obj, Scheme.Pullback.openCoverOfRight_map,
      limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app, Category.comp_id]
    apply this _ (comp_of_isOpenImmersion _ _ _ H) inferInstance
  rw [iff_of_isAffine (P := P)] at H ⊢
  exact hP.pullback_fst_app_top _ (isLocal_ringHomProperty P).respectsIso _ _ H

end HasRingHomProperty

end AlgebraicGeometry

/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Basic
import Mathlib.RingTheory.RingHomProperties

/-!

# Constructors for properties of morphisms between schemes

This file provides some constructors to obtain morphism properties of schemes from other morphism
properties:

- `AffineTargetMorphismProperty.diagonal` : Given an affine target morphism property `P`,
  `P.diagonal f` holds if `P (pullback.mapDesc f₁ f₂ f)` holds for two affine open
  immersions `f₁` and `f₂`.
- `AffineTargetMorphismProperty.of`: Given a morphism property `P` of schemes,
  this is the restriction of `P` to morphisms with affine target. If `P` is local at the
  target, we have `(toAffineTargetMorphismProperty P).targetAffineLocally = P`
  (see `MorphismProperty.targetAffineLocally_toAffineTargetMorphismProperty_eq_of_isLocalAtTarget`).
- `MorphismProperty.topologically`: Given a property `P` of maps of topological spaces,
  `(topologically P) f` holds if `P` holds for the underlying continuous map of `f`.
- `MorphismProperty.stalkwise`: Given a property `P` of ring homs,
  `(stalkwise P) f` holds if `P` holds for all stalk maps.

Also provides API for showing the standard locality and stability properties for these
types of properties.

-/

universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

section Diagonal

/-- The `AffineTargetMorphismProperty` associated to `(targetAffineLocally P).diagonal`.
See `diagonal_targetAffineLocally_eq_targetAffineLocally`.
-/
def AffineTargetMorphismProperty.diagonal (P : AffineTargetMorphismProperty) :
    AffineTargetMorphismProperty :=
  fun {X _} f _ =>
    ∀ ⦃U₁ U₂ : Scheme⦄ (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)
#align algebraic_geometry.affine_target_morphism_property.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.diagonal

instance AffineTargetMorphismProperty.diagonal_respectsIso (P : AffineTargetMorphismProperty)
    [P.toProperty.RespectsIso] : P.diagonal.toProperty.RespectsIso := by
  delta AffineTargetMorphismProperty.diagonal
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H _ _
    rw [pullback.mapDesc_comp, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
    apply H
  · introv H _ _
    rw [pullback.mapDesc_comp, P.cancel_right_of_respectsIso]
    apply H
#align algebraic_geometry.affine_target_morphism_property.diagonal_respects_iso AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso

theorem HasAffineProperty.diagonal_of_openCover
    (P) [HasAffineProperty P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) [∀ i j, IsAffine ((𝒰' i).obj j)]
    (h𝒰' : ∀ i j k,
      P.affineProperty (pullback.mapDesc ((𝒰' i).map j) ((𝒰' i).map k) (𝒰.pullbackHom f i))) :
    P.diagonal f := by
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : ∀ i, IsAffine (𝒱.obj i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert (P.affineProperty.cancel_left_of_respectsIso
    ((pullbackDiagonalMapIso _ _ ((𝒰' i).map j) ((𝒰' i).map k)).inv ≫
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _) pullback.snd).mp _ using 1
  · simp
  · ext <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Functor.const_obj_obj, cospan_one, cospan_left, cospan_right, Category.comp_id]
    convert h𝒰' i j k
    ext <;> simp [Scheme.OpenCover.pullbackHom]
#align algebraic_geometry.diagonal_target_affine_locally_of_open_cover AlgebraicGeometry.HasAffineProperty.diagonal_of_openCover

theorem HasAffineProperty.diagonal_of_openCover_diagonal_affineProperty
    (P) [HasAffineProperty P]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (h𝒰 : ∀ i, P.affineProperty.diagonal (𝒰.pullbackHom f i)) :
    P.diagonal f :=
  HasAffineProperty.diagonal_of_openCover P f 𝒰 (fun _ ↦ Scheme.affineCover _)
    (fun _ _ _ ↦ h𝒰 _ _ _)

instance {X} [IsAffine X] (i) : IsAffine ((Scheme.openCoverOfIsIso (𝟙 X)).obj i) := by
  dsimp; infer_instance

theorem HasAffineProperty.affineProperty_diagonal_of_diagonal_of_isPullback
    (P) [HasAffineProperty P]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y}
    [IsAffine U] [IsOpenImmersion g]
    {iV : V ⟶ X} {f' : V ⟶ U} (h : IsPullback iV f' f g) (H : P.diagonal f) :
    P.affineProperty.diagonal f' := by
  rw [← P.affineProperty.diagonal.cancel_left_of_respectsIso h.isoPullback.inv,
    h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← P.affineProperty.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance
#align algebraic_geometry.affine_target_morphism_property.diagonal_of_target_affine_locally AlgebraicGeometry.HasAffineProperty.affineProperty_diagonal_of_diagonal_of_isPullback

lemma _root_.CategoryTheory.IsPullback.of_id_fst {C} [Category C] {X Y : C} (f : X ⟶ Y) :
    IsPullback (𝟙 _) f f (𝟙 _) := IsPullback.of_horiz_isIso ⟨by simp⟩

lemma _root_.CategoryTheory.IsPullback.of_id_snd {C} [Category C] {X Y : C} (f : X ⟶ Y) :
  IsPullback f (𝟙 _) (𝟙 _) f := IsPullback.of_vert_isIso ⟨by simp⟩

theorem HasAffineProperty.of_affineProperty_diagonal
    {P} [HasAffineProperty P] {X Y} {f : X ⟶ Y} [IsAffine Y] :
    P.affineProperty.diagonal f ↔ P.diagonal f := by
  refine ⟨fun hf ↦ ?_, affineProperty_diagonal_of_diagonal_of_isPullback P (.of_id_fst _)⟩
  rw [← P.affineProperty.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y)), pullback.condition, Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i) : IsAffine (𝒰.obj i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover P f (Scheme.openCoverOfIsIso (𝟙 _))
    (fun _ ↦ 𝒰) (fun _ _ _ ↦ hf _ _)

theorem HasAffineProperty.affineProperty_diagonal (P) [HasAffineProperty P] :
    P.affineProperty.diagonal = AffineTargetMorphismProperty.of P.diagonal := by
  ext X Y f _
  exact of_affineProperty_diagonal

instance HasAffineProperty.diagonal_affineProperty_isLocal (P) [HasAffineProperty P] :
    P.affineProperty.diagonal.IsLocal where
  respectsIso := inferInstance
  to_basicOpen {X Y} _ f r hf :=
    have : IsAffine (Y ∣_ᵤ Y.basicOpen r) := (isAffineOpen_top Y).basicOpen r
    affineProperty_diagonal_of_diagonal_of_isPullback P
      (isPullback_morphismRestrict f (Y.basicOpen r)).flip
      (of_affineProperty_diagonal.mp hf)
  of_basicOpenCover {X Y} _ f s hs hs' := by
    refine of_affineProperty_diagonal.mpr ?_
    let 𝒰 := Y.openCoverOfSuprEqTop _ (((isAffineOpen_top Y).basicOpen_union_eq_self_iff _).mpr hs)
    have (i) : IsAffine (𝒰.obj i) := (isAffineOpen_top Y).basicOpen i.1
    refine diagonal_of_openCover_diagonal_affineProperty P f
      (Y.openCoverOfSuprEqTop _ (((isAffineOpen_top Y).basicOpen_union_eq_self_iff _).mpr hs)) ?_
    intro i
    exact (P.affineProperty.diagonal.arrow_mk_iso_iff
      (morphismRestrictEq _ (by simp) ≪≫ morphismRestrictOpensRange _ _)).mp (hs' i)
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal AlgebraicGeometry.HasAffineProperty.diagonal_affineProperty_isLocal

theorem HasAffineProperty.targetAffineLocally_diagonal_affineProperty (P) [HasAffineProperty P] :
    targetAffineLocally P.affineProperty.diagonal = P.diagonal := by
  ext X Y f
  constructor
  · exact fun H ↦ diagonal_of_openCover_diagonal_affineProperty P f Y.affineCover
      (fun i ↦ of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) H)
  · exact fun H U ↦ affineProperty_diagonal_of_diagonal_of_isPullback P
      (isPullback_morphismRestrict f U).flip H
#align algebraic_geometry.diagonal_target_affine_locally_eq_target_affine_locally AlgebraicGeometry.HasAffineProperty.targetAffineLocally_diagonal_affineProperty

instance (P) [HasAffineProperty P] : HasAffineProperty P.diagonal where
  affineProperty := P.affineProperty.diagonal
  isLocal_affineProperty := inferInstance
  eq_targetAffineLocally' := (HasAffineProperty.targetAffineLocally_diagonal_affineProperty P).symm

instance (P) [IsLocalAtTarget P] : IsLocalAtTarget P.diagonal :=
  letI := hasAffinePropertyOfIsLocalAtTarget P
  inferInstance

end Diagonal

section Universally

theorem universally_isLocalAtTarget (P : MorphismProperty Scheme)
    [P.RespectsIso]
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y.carrier)
      (_ : iSup U = ⊤), (∀ i, P (f ∣_ U i)) → P f) : IsLocalAtTarget P.universally := by
  refine ⟨P.universally_respectsIso, fun {X Y} f U =>
    P.universally_stableUnderBaseChange (isPullback_morphismRestrict f U).flip, ?_⟩
  intros X Y f Us hUs H X' Y' i₁ i₂ f' h
  apply hP₂ _ (fun i : Us ↦ i₂ ⁻¹ᵁ i.1)
  · rw [← top_le_iff] at hUs ⊢
    rintro x -
    simpa using @hUs (i₂.1.base x) trivial
  · rintro U
    refine H _ U.2 ((X'.restrictIsoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
    · exact congr($(h.1.1) ⁻¹ᵁ U.1)
    · rw [← (isPullback_morphismRestrict f U.1).paste_vert_iff]
      · simp only [Scheme.restrictIsoOfEq, Category.assoc, morphismRestrict_ι,
          IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
        exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U)).paste_vert h
      · rw [← cancel_mono (Scheme.ιOpens _)]
        simp [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Scheme.restrictIsoOfEq,
          morphismRestrict_ι_assoc, h.1.1]

#align algebraic_geometry.universally_is_local_at_target_of_morphism_restrict AlgebraicGeometry.universally_isLocalAtTarget

end Universally

namespace MorphismProperty

section Topologically

/-- `topologically P` holds for a morphism if the underlying topological map satisfies `P`. -/
def topologically
    (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop) :
    MorphismProperty Scheme.{u} := fun _ _ f => P f.1.base
#align algebraic_geometry.morphism_property.topologically AlgebraicGeometry.MorphismProperty.topologically

variable (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop)

/-- If a property of maps of topological spaces is stable under composition, the induced
morphism property of schemes is stable under composition. -/
lemma topologically_isStableUnderComposition
    (hP : ∀ {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α → β) (g : β → γ) (_ : P f) (_ : P g), P (g ∘ f)) :
    (MorphismProperty.topologically P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    simp only [MorphismProperty.topologically, Scheme.comp_coeBase, TopCat.coe_comp]
    exact hP _ _ hf hg

/-- If a property of maps of topological spaces is satisfied by all homeomorphisms,
every isomorphism of schemes satisfies the induced property. -/
lemma topologically_iso_le
    (hP : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f) :
    MorphismProperty.isomorphisms Scheme ≤ (MorphismProperty.topologically P) := by
  intro X Y e (he : IsIso e)
  have : IsIso e := he
  exact hP (TopCat.homeoOfIso (asIso e.val.base))

/-- If a property of maps of topological spaces is satisfied by homeomorphisms and is stable
under composition, the induced property on schemes respects isomorphisms. -/
lemma topologically_respectsIso
    (hP₁ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f)
    (hP₂ : ∀ {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α → β) (g : β → γ) (_ : P f) (_ : P g), P (g ∘ f)) :
      (MorphismProperty.topologically P).RespectsIso :=
  have : (MorphismProperty.topologically P).IsStableUnderComposition :=
    topologically_isStableUnderComposition P hP₂
  MorphismProperty.respectsIso_of_isStableUnderComposition (topologically_iso_le P hP₁)

/-- To check that a topologically defined morphism property is local at the target,
we may check the corresponding properties on topological spaces. -/
lemma topologically_propertyIsLocalAtTarget
    [(MorphismProperty.topologically P).RespectsIso]
    (hP₂ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) (s : Set β),
      P f → P (s.restrictPreimage f))
    (hP₃ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) {ι : Type u}
      (U : ι → TopologicalSpace.Opens β) (_ : iSup U = ⊤) (_ : Continuous f),
      (∀ i, P ((U i).carrier.restrictPreimage f)) → P f) :
    IsLocalAtTarget (MorphismProperty.topologically P) := by
  constructor
  · infer_instance
  · intro X Y f U hf
    simp_rw [MorphismProperty.topologically, morphismRestrict_val_base]
    exact hP₂ f.val.base U.carrier hf
  · intro X Y f Us hU hf
    apply hP₃ f.val.base (fun i : Us ↦ i.1) (by simpa using hU) f.val.base.continuous fun i ↦ ?_
    rw [← morphismRestrict_val_base]
    exact hf i i.2

end Topologically

/-- `stalkwise P` holds for a morphism if all stalks satisfy `P`. -/
def stalkwise (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) :
    MorphismProperty Scheme.{u} :=
  fun _ _ f => ∀ x, P (PresheafedSpace.stalkMap f.val x)

section Stalkwise

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- If `P` respects isos, then `stalkwise P` respects isos. -/
lemma stalkwise_respectsIso (hP : RingHom.RespectsIso P) :
    (MorphismProperty.stalkwise P).RespectsIso where
  precomp {X Y Z} e f hf := by
    simp only [stalkwise, Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
    intro x
    erw [PresheafedSpace.stalkMap.comp]
    exact (RingHom.RespectsIso.cancel_right_isIso hP _ _).mpr <| hf (e.hom.val.base x)
  postcomp {X Y Z} e f hf := by
    simp only [stalkwise, Scheme.comp_coeBase, TopCat.coe_comp, Function.comp_apply]
    intro x
    erw [PresheafedSpace.stalkMap.comp]
    exact (RingHom.RespectsIso.cancel_left_isIso hP _ _).mpr <| hf x

/-- If `P` respects isos, then `stalkwise P` is local at the target. -/
lemma stalkwiseIsLocalAtTarget_of_respectsIso (hP : RingHom.RespectsIso P) :
    PropertyIsLocalAtTarget (MorphismProperty.stalkwise P) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  letI := stalkwise_respectsIso hP
  apply propertyIsLocalAtTarget_of_morphismRestrict
  · intro X Y f U hf x
    apply ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f U x).mpr <| hf _
  · intro X Y f ι U hU hf x
    have hy : f.val.base x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f (U i) ⟨x, hi⟩).mp <| hf i ⟨x, hi⟩

end Stalkwise

end MorphismProperty

section Restriction

/-- If `P` is a property of scheme morphisms, we may restrict `P` to morphisms with affine target
to obtain an `AffineTargetMorphismProperty`. -/
def AffineTargetMorphismProperty.of (P : MorphismProperty Scheme) :
    AffineTargetMorphismProperty := fun _ _ f ↦ P f

namespace AffineTargetMorphismProperty

/-- Restricting a local at the target morphism property of schemes `P` to morphisms with affine
target and extending to a global property with `targetAffineLocally` yields `P` again,
if `P` is local at the target. -/
lemma targetAffineLocally_of_eq_of_isLocalAtTarget
    (P : MorphismProperty Scheme) (hP : PropertyIsLocalAtTarget P) :
    targetAffineLocally (of P) = P := by
  ext X Y f
  constructor
  · intro hf
    simp only [targetAffineLocally, Subtype.forall] at hf
    let 𝒰 : Y.OpenCover := Y.affineCover
    apply hP.of_openCover f 𝒰
    intro i
    have hiao : IsAffineOpen (Scheme.Hom.opensRange (𝒰.map i)) :=
      AlgebraicGeometry.isAffineOpen_opensRange _
    letI : P.RespectsIso := hP.RespectsIso
    rw [← P.arrow_mk_iso_iff <| morphismRestrictOpensRange f (𝒰.map i)]
    exact hf (Scheme.Hom.opensRange (𝒰.map i)) hiao
  · intro hf ⟨U, hU⟩
    exact hP.restrict _ _ hf

/-- The restriction of a morphism property of schemes that is local at the target to morphisms
with affine target, is local. -/
lemma of_isLocal_of_isLocalAtTarget (P : MorphismProperty Scheme)
    (hP : PropertyIsLocalAtTarget P) : (of P).IsLocal where
  RespectsIso := by
    apply AffineTargetMorphismProperty.respectsIso_mk
    · intro X Y Z e f _ hf
      apply hP.RespectsIso.precomp e f hf
    · intro X Y Z e f _ hf
      apply hP.RespectsIso.postcomp e f hf
  toBasicOpen {X Y} _ f hf := hP.restrict f _
  ofBasicOpenCover {X Y} _ f s hs hf := by
    apply ((hP.openCover_TFAE f).out 0 5).mpr
    let U (r : s) : Opens Y.carrier := Y.basicOpen r.val
    have hiao : IsAffineOpen (⊤ : Opens Y.carrier) := isAffineOpen_top Y
    have hU : iSup U = ⊤ := by
      erw [hiao.basicOpen_union_eq_self_iff]
      exact hs
    use s, U, hU, hf

/-- If `P` is local at the target, to show that `P` is stable under base change, it suffices to
check this for base change along a morphism of affine schemes. -/
lemma stableUnderBaseChange_of_stableUnderBaseChangeOnAffine_of_isLocalAtTarget
    (P : MorphismProperty Scheme) (hP₁ : PropertyIsLocalAtTarget P)
    (hP₂ : (of P).StableUnderBaseChange) :
    P.StableUnderBaseChange := by
  rw [← targetAffineLocally_of_eq_of_isLocalAtTarget P hP₁]
  apply (of_isLocal_of_isLocalAtTarget P hP₁).stableUnderBaseChange
  exact hP₂

end AffineTargetMorphismProperty

end Restriction

@[deprecated (since := "2024-06-22")]
alias diagonalTargetAffineLocallyOfOpenCover := HasAffineProperty.diagonal_of_openCover

@[deprecated (since := "2024-06-22")]
alias AffineTargetMorphismProperty.diagonalOfTargetAffineLocally :=
  HasAffineProperty.affineProperty_diagonal_of_diagonal_of_isPullback

@[deprecated (since := "2024-06-22")]
alias universallyIsLocalAtTarget := universally_isLocalAtTarget

@[deprecated (since := "2024-06-22")]
alias universallyIsLocalAtTargetOfMorphismRestrict :=
  universally_isLocalAtTarget

end AlgebraicGeometry

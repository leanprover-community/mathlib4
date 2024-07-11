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
    ∀ {U₁ U₂ : Scheme} (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)
#align algebraic_geometry.affine_target_morphism_property.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.diagonal

instance AffineTargetMorphismProperty.diagonal_respectsIso (P : AffineTargetMorphismProperty)
    [P.toProperty.RespectsIso] : P.diagonal.toProperty.RespectsIso := by
  delta AffineTargetMorphismProperty.diagonal
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H _ _
    rw [pullback.mapDesc_comp, P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
    -- Porting note: add the following two instances
    have i1 : IsOpenImmersion (f₁ ≫ e.hom) := PresheafedSpace.IsOpenImmersion.comp _ _
    have i2 : IsOpenImmersion (f₂ ≫ e.hom) := PresheafedSpace.IsOpenImmersion.comp _ _
    apply H
  · introv H _ _
    -- Porting note: add the following two instances
    have _ : IsAffine Z := isAffine_of_isIso e.inv
    rw [pullback.mapDesc_comp, P.cancel_right_of_respectsIso]
    apply H
#align algebraic_geometry.affine_target_morphism_property.diagonal_respects_iso AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso

theorem diagonal_targetAffineLocally_of_openCover
    (P : AffineTargetMorphismProperty) (hP : P.IsLocal)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) [∀ i j, IsAffine ((𝒰' i).obj j)]
    (h𝒰' : ∀ i j k, P (pullback.mapDesc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)) :
    (targetAffineLocally P).diagonal f := by
  have := hP.1
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) pullback.snd pullback.snd
  have i1 : ∀ i, IsAffine (𝒱.obj i) := fun i => by dsimp [𝒱]; infer_instance
  apply (hP.affine_openCover_iff _ 𝒱).mpr
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert (P.cancel_left_of_respectsIso
    (pullbackDiagonalMapIso _ _ ((𝒰' i).map j) ((𝒰' i).map k)).inv pullback.snd).mp _
  pick_goal 3
  · convert h𝒰' i j k; apply pullback.hom_ext <;> simp
  all_goals apply pullback.hom_ext <;>
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
    pullback.lift_snd_assoc]
#align algebraic_geometry.diagonal_target_affine_locally_of_open_cover AlgebraicGeometry.diagonal_targetAffineLocally_of_openCover

theorem AffineTargetMorphismProperty.diagonal_of_targetAffineLocally
    (P : AffineTargetMorphismProperty) (hP : P.IsLocal) {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
    [IsAffine U] [IsOpenImmersion g] (H : (targetAffineLocally P).diagonal f) :
    P.diagonal (pullback.snd : pullback f g ⟶ _) := by
  have := hP.1
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  replace H := ((hP.affine_openCover_TFAE (pullback.diagonal f)).out 0 3).mp H
  let g₁ := pullback.map (f₁ ≫ pullback.snd) (f₂ ≫ pullback.snd) f f
    (f₁ ≫ pullback.fst) (f₂ ≫ pullback.fst) g
    (by rw [Category.assoc, Category.assoc, pullback.condition])
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  specialize H g₁
  rw [← P.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert H
  apply pullback.hom_ext <;>
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.comp_id, pullbackDiagonalMapIso_hom_fst,
      pullbackDiagonalMapIso_hom_snd]
#align algebraic_geometry.affine_target_morphism_property.diagonal_of_target_affine_locally AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_of_targetAffineLocally

open List in
theorem AffineTargetMorphismProperty.IsLocal.diagonal_affine_openCover_TFAE
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [(targetAffineLocally P).diagonal f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, P.diagonal (pullback.snd : pullback f (𝒰.map i) ⟶ _),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          P.diagonal (pullback.snd : pullback f (𝒰.map i) ⟶ _),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g],
          P.diagonal (pullback.snd : pullback f g ⟶ _),
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)) (𝒰' :
          ∀ i, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) (_ : ∀ i j, IsAffine ((𝒰' i).obj j)),
          ∀ i j k, P (pullback.mapDesc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)] := by
  tfae_have 1 → 4
  · introv H hU hg _ _; apply P.diagonal_of_targetAffineLocally <;> assumption
  tfae_have 4 → 3
  · introv H h𝒰; apply H
  tfae_have 3 → 2
  · exact fun H => ⟨Y.affineCover, inferInstance, H Y.affineCover⟩
  tfae_have 2 → 5
  · rintro ⟨𝒰, h𝒰, H⟩
    refine ⟨𝒰, inferInstance, fun _ => Scheme.affineCover _, inferInstance, ?_⟩
    intro i j k
    apply H
  tfae_have 5 → 1
  · rintro ⟨𝒰, _, 𝒰', _, H⟩
    exact diagonal_targetAffineLocally_of_openCover P hP f 𝒰 𝒰' H
  tfae_finish
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal_affine_open_cover_tfae AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.diagonal_affine_openCover_TFAE

theorem AffineTargetMorphismProperty.IsLocal.diagonal {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) : P.diagonal.IsLocal :=
  have := hP.1
  AffineTargetMorphismProperty.isLocalOfOpenCoverImply P.diagonal
    fun {_ _} f => ((hP.diagonal_affine_openCover_TFAE f).out 1 3).mp
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.diagonal

theorem diagonal_targetAffineLocally_eq_targetAffineLocally (P : AffineTargetMorphismProperty)
    (hP : P.IsLocal) : (targetAffineLocally P).diagonal = targetAffineLocally P.diagonal := by
  ext _ _ f
  exact ((hP.diagonal_affine_openCover_TFAE f).out 0 1).trans
    ((hP.diagonal.affine_openCover_TFAE f).out 1 0)
#align algebraic_geometry.diagonal_target_affine_locally_eq_target_affine_locally AlgebraicGeometry.diagonal_targetAffineLocally_eq_targetAffineLocally

end Diagonal

section Universally

theorem universally_isLocalAtTarget (P : MorphismProperty Scheme)
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
      (∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) → P f) :
    PropertyIsLocalAtTarget P.universally := by
  refine ⟨P.universally_respectsIso, fun {X Y} f U =>
    P.universally_stableUnderBaseChange (isPullback_morphismRestrict f U).flip, ?_⟩
  intro X Y f 𝒰 h X' Y' i₁ i₂ f' H
  apply hP _ (𝒰.pullbackCover i₂)
  intro i
  dsimp
  apply h i (pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ pullback.snd) _) pullback.snd
  swap
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition_assoc, H.w]
  refine (IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)).flip
  rw [pullback.lift_fst, ← pullback.condition]
  exact (IsPullback.of_hasPullback _ _).paste_horiz H.flip
#align algebraic_geometry.universally_is_local_at_target AlgebraicGeometry.universally_isLocalAtTarget

theorem universally_isLocalAtTarget_of_morphismRestrict (P : MorphismProperty Scheme)
    [P.RespectsIso]
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y.carrier)
      (_ : iSup U = ⊤), (∀ i, P (f ∣_ U i)) → P f) : PropertyIsLocalAtTarget P.universally :=
  universally_isLocalAtTarget P (fun f 𝒰 h𝒰 => by
    apply hP₂ f (fun i : 𝒰.J => Scheme.Hom.opensRange (𝒰.map i)) 𝒰.iSup_opensRange
    simp_rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    exact h𝒰)
#align algebraic_geometry.universally_is_local_at_target_of_morphism_restrict AlgebraicGeometry.universally_isLocalAtTarget_of_morphismRestrict

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
    PropertyIsLocalAtTarget (MorphismProperty.topologically P) := by
  apply propertyIsLocalAtTarget_of_morphismRestrict
  · intro X Y f U hf
    simp_rw [MorphismProperty.topologically, morphismRestrict_val_base]
    exact hP₂ f.val.base U.carrier hf
  · intro X Y f ι U hU hf
    apply hP₃ f.val.base U hU
    · exact f.val.base.continuous
    · intro i
      rw [← morphismRestrict_val_base]
      exact hf i

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
alias diagonalTargetAffineLocallyOfOpenCover := diagonal_targetAffineLocally_of_openCover

@[deprecated (since := "2024-06-22")]
alias AffineTargetMorphismProperty.diagonalOfTargetAffineLocally :=
  AffineTargetMorphismProperty.diagonal_of_targetAffineLocally

@[deprecated (since := "2024-06-22")]
alias universallyIsLocalAtTarget := universally_isLocalAtTarget

@[deprecated (since := "2024-06-22")]
alias universallyIsLocalAtTargetOfMorphismRestrict :=
  universally_isLocalAtTarget_of_morphismRestrict

end AlgebraicGeometry

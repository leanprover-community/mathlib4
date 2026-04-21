/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Basic
public import Mathlib.RingTheory.RingHomProperties

/-!

# Constructors for properties of morphisms between schemes

This file provides some constructors to obtain morphism properties of schemes from other morphism
properties:

- `AffineTargetMorphismProperty.diagonal` : Given an affine target morphism property `P`,
  `P.diagonal f` holds if `P (pullback.mapDesc f₁ f₂ f)` holds for two affine open
  immersions `f₁` and `f₂`.
- `AffineTargetMorphismProperty.of`: Given a morphism property `P` of schemes,
  this is the restriction of `P` to morphisms with affine target. If `P` is local at the
  target, we have `(toAffineTargetMorphismProperty P).targetAffineLocally = P`, see:
  `MorphismProperty.targetAffineLocally_toAffineTargetMorphismProperty_eq_of_isZariskiLocalAtTarget`
- `MorphismProperty.topologically`: Given a property `P` of maps of topological spaces,
  `(topologically P) f` holds if `P` holds for the underlying continuous map of `f`.
- `MorphismProperty.stalkwise`: Given a property `P` of ring homomorphisms,
  `(stalkwise P) f` holds if `P` holds for all stalk maps.

Also provides API for showing the standard locality and stability properties for these
types of properties.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

universe u v w

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

set_option backward.isDefEq.respectTransparency false in
theorem HasAffineProperty.diagonal_of_openCover (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} Y) [∀ i, IsAffine (𝒰.X i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{w} (pullback f (𝒰.f i))) [∀ i j, IsAffine ((𝒰' i).X j)]
    (h𝒰' : ∀ i j k,
      Q (pullback.mapDesc ((𝒰' i).f j) ((𝒰' i).f k) (𝒰.pullbackHom f i))) :
    P.diagonal f := by
  letI := isLocal_affineProperty P
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) (pullback.snd _ _) (pullback.snd _ _)
  have i1 : ∀ i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  apply of_openCover 𝒱
  rintro ⟨i, j, k⟩
  dsimp [𝒱]
  convert (Q.cancel_left_of_respectsIso
    ((pullbackDiagonalMapIso _ _ ((𝒰' i).f j) ((𝒰' i).f k)).inv ≫
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _) (pullback.snd _ _)).mp _ using 1
  · simp
  · ext1 <;> simp
  · simp only [Category.assoc, limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app,
      Category.comp_id]
    convert h𝒰' i j k
    ext1 <;> simp [Scheme.Cover.pullbackHom]

theorem HasAffineProperty.diagonal_of_openCover_diagonal
    (P) {Q} [HasAffineProperty P Q]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover Y) [∀ i, IsAffine (𝒰.X i)]
    (h𝒰 : ∀ i, Q.diagonal (𝒰.pullbackHom f i)) :
    P.diagonal f :=
  diagonal_of_openCover P f 𝒰 (fun _ ↦ Scheme.affineCover _)
    (fun _ _ _ ↦ h𝒰 _ _ _)

set_option backward.isDefEq.respectTransparency false in
theorem HasAffineProperty.diagonal_of_diagonal_of_isPullback
    (P) {Q} [HasAffineProperty P Q]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {g : U ⟶ Y}
    [IsAffine U] [IsOpenImmersion g]
    {iV : V ⟶ X} {f' : V ⟶ U} (h : IsPullback iV f' f g) (H : P.diagonal f) :
    Q.diagonal f' := by
  letI := isLocal_affineProperty P
  rw [← Q.diagonal.cancel_left_of_respectsIso h.isoPullback.inv,
    h.isoPullback_inv_snd]
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  rw [← Q.cancel_left_of_respectsIso (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  convert HasAffineProperty.of_isPullback (P := P) (.of_hasPullback _ _) H
  · apply pullback.hom_ext <;> simp
  · infer_instance
  · infer_instance

theorem HasAffineProperty.diagonal_iff
    (P) {Q} [HasAffineProperty P Q] {X Y : Scheme.{u}} {f : X ⟶ Y} [IsAffine Y] :
    Q.diagonal f ↔ P.diagonal f := by
  letI := isLocal_affineProperty P
  refine ⟨fun hf ↦ ?_, diagonal_of_diagonal_of_isPullback P .of_id_fst⟩
  rw [← Q.diagonal.cancel_left_of_respectsIso
    (pullback.fst (f := f) (g := 𝟙 Y)), pullback.condition, Category.comp_id] at hf
  let 𝒰 := X.affineCover.pushforwardIso (inv (pullback.fst (f := f) (g := 𝟙 Y)))
  have (i : _) : IsAffine (𝒰.X i) := by dsimp [𝒰]; infer_instance
  exact HasAffineProperty.diagonal_of_openCover.{u, u, u} P f (Scheme.coverOfIsIso (𝟙 _))
    (fun _ ↦ 𝒰) (fun _ _ _ ↦ hf _ _)

set_option backward.isDefEq.respectTransparency false in
theorem AffineTargetMorphismProperty.diagonal_of_openCover_source
    {Q : AffineTargetMorphismProperty} [Q.IsLocal]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{v} X) [∀ i, IsAffine (𝒰.X i)]
    [IsAffine Y] (h𝒰 : ∀ i j, Q (pullback.mapDesc (𝒰.f i) (𝒰.f j) f)) :
    Q.diagonal f := by
  rw [HasAffineProperty.diagonal_iff (targetAffineLocally Q)]
  let 𝒱 := Scheme.Pullback.openCoverOfLeftRight.{u} 𝒰 𝒰 f f
  have i1 : ∀ i, IsAffine (𝒱.X i) := fun i => by dsimp [𝒱]; infer_instance
  refine HasAffineProperty.of_openCover (P := targetAffineLocally Q) 𝒱 fun i ↦ ?_
  dsimp [𝒱, Scheme.Cover.pullbackHom]
  have : IsPullback (pullback.fst _ _ ≫ 𝒰.f _) (pullback.mapDesc (𝒰.f i.1) (𝒰.f i.2) f)
      (pullback.diagonal f) (pullback.map _ _ _ _ (𝒰.f _) (𝒰.f _) (𝟙 Y) (by simp) (by simp)) :=
    .of_iso (pullback_fst_map_snd_isPullback f (𝟙 _) (𝒰.f i.1 ≫ pullback.lift (𝟙 _) f)
      (𝒰.f i.2 ≫ pullback.lift (𝟙 _) f)) (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _)
      (pullback.fst _ _) (by simp) (by simp))) (.refl _) (pullback.congrHom (by simp) (by simp))
      (.refl _) (by simp) (by cat_disch) (by simp) (by cat_disch)
  rw [← Q.cancel_left_of_respectsIso this.isoPullback.hom, IsPullback.isoPullback_hom_snd]
  exact h𝒰 _ _

instance HasAffineProperty.diagonal_affineProperty_isLocal
    {Q : AffineTargetMorphismProperty} [Q.IsLocal] :
    Q.diagonal.IsLocal where
  respectsIso := inferInstance
  to_basicOpen {_ Y} _ f r hf :=
    diagonal_of_diagonal_of_isPullback (targetAffineLocally Q)
      (isPullback_morphismRestrict f (Y.basicOpen r)).flip
      ((diagonal_iff (targetAffineLocally Q)).mp hf)
  of_basicOpenCover {X Y} _ f s hs hs' := by
    refine (diagonal_iff (targetAffineLocally Q)).mpr ?_
    let 𝒰 := Y.openCoverOfIsOpenCover _
      ((isAffineOpen_top Y).iSup_basicOpen_eq_self_iff.mpr hs)
    have (i : _) : IsAffine (𝒰.X i) := (isAffineOpen_top Y).basicOpen i.1
    refine diagonal_of_openCover_diagonal (targetAffineLocally Q) f 𝒰 ?_
    intro i
    exact (Q.diagonal.arrow_mk_iso_iff
      (morphismRestrictEq _ (by simp [𝒰]) ≪≫ morphismRestrictOpensRange _ _)).mp (hs' i)

instance (P) {Q} [HasAffineProperty P Q] : HasAffineProperty P.diagonal Q.diagonal where
  isLocal_affineProperty := letI := HasAffineProperty.isLocal_affineProperty P; inferInstance
  eq_targetAffineLocally' := by
    ext X Y f
    letI := HasAffineProperty.isLocal_affineProperty P
    constructor
    · exact fun H U ↦ HasAffineProperty.diagonal_of_diagonal_of_isPullback P
        (isPullback_morphismRestrict f U).flip H
    · exact fun H ↦ HasAffineProperty.diagonal_of_openCover_diagonal P f Y.affineCover
        (fun i ↦ of_targetAffineLocally_of_isPullback (.of_hasPullback _ _) H)

instance (P) [IsZariskiLocalAtTarget P] : IsZariskiLocalAtTarget P.diagonal :=
  letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  inferInstance

open MorphismProperty in
instance (P : MorphismProperty Scheme)
    [P.HasOfPostcompProperty @IsOpenImmersion] [P.RespectsRight @IsOpenImmersion]
    [IsZariskiLocalAtSource P] : IsZariskiLocalAtSource P.diagonal := by
  let g {X Y : Scheme} (f : X ⟶ Y) (U : X.Opens) :=
    pullback.map (U.ι ≫ f) (U.ι ≫ f) f f U.ι U.ι (𝟙 Y) (by simp) (by simp)
  refine IsZariskiLocalAtSource.mk' (fun {X Y} f U hf ↦ ?_) (fun {X Y} f {ι} U hU hf ↦ ?_)
  · change P _
    apply P.of_postcomp (W' := @IsOpenImmersion) (pullback.diagonal (U.ι ≫ f)) (g f U) inferInstance
    rw [← pullback.comp_diagonal]
    apply IsZariskiLocalAtSource.comp
    exact hf
  · change P _
    refine IsZariskiLocalAtSource.of_iSup_eq_top U hU fun i ↦ ?_
    rw [pullback.comp_diagonal]
    exact RespectsRight.postcomp (P := P) (Q := @IsOpenImmersion) (g _ _) inferInstance _ (hf i)

end Diagonal

section Universally

theorem universally_isZariskiLocalAtTarget (P : MorphismProperty Scheme)
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Y.Opens)
      (_ : IsOpenCover U), (∀ i, P (f ∣_ U i)) → P f) : IsZariskiLocalAtTarget P.universally := by
  apply IsZariskiLocalAtTarget.mk'
  · exact fun {X Y} f U => P.universally.of_isPullback
      (isPullback_morphismRestrict f U).flip
  · intro X Y f ι U hU H X' Y' i₁ i₂ f' h
    apply hP₂ _ (fun i ↦ i₂ ⁻¹ᵁ U i)
    · simp only [IsOpenCover, ← top_le_iff] at hU ⊢
      rintro x -
      simpa using @hU (i₂ x) trivial
    · rintro i
      refine H _ ((X'.isoOfEq ?_).hom ≫ i₁ ∣_ _) (i₂ ∣_ _) _ ?_
      · exact congr($(h.1.1) ⁻¹ᵁ U i)
      · rw [← (isPullback_morphismRestrict f _).paste_vert_iff]
        · simp only [Category.assoc, morphismRestrict_ι, Scheme.isoOfEq_hom_ι_assoc]
          exact (isPullback_morphismRestrict f' (i₂ ⁻¹ᵁ U i)).paste_vert h
        · rw [← cancel_mono (Scheme.Opens.ι _)]
          simp [morphismRestrict_ι_assoc, h.1.1]

lemma universally_isZariskiLocalAtSource (P : MorphismProperty Scheme)
    [IsZariskiLocalAtSource P] : IsZariskiLocalAtSource P.universally := by
  refine .mk_of_iff ?_
  intro X Y f 𝒰
  refine ⟨fun hf i ↦ ?_, fun hf ↦ ?_⟩
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [← P.cancel_left_of_respectsIso (pullbackLeftPullbackSndIso g f _).hom,
      pullbackLeftPullbackSndIso_hom_fst]
    exact IsZariskiLocalAtSource.comp (hf _ _ _ (IsPullback.of_hasPullback ..)) _
  · apply MorphismProperty.universally_mk'
    intro T g _
    rw [IsZariskiLocalAtSource.iff_of_openCover (P := P) (𝒰.pullback₁ <| pullback.snd g f)]
    intro i
    dsimp only [Precoverage.ZeroHypercover.pullback₁_toPreZeroHypercover,
      PreZeroHypercover.pullback₁_X, PreZeroHypercover.pullback₁_f]
    rw [← pullbackLeftPullbackSndIso_hom_fst, P.cancel_left_of_respectsIso]
    exact hf i _ _ _ (IsPullback.of_hasPullback ..)

end Universally

section Topologically

/-- `topologically P` holds for a morphism if the underlying topological map satisfies `P`. -/
def topologically
    (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop) :
    MorphismProperty Scheme.{u} := fun _ _ f => P f

variable (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop)

/-- If a property of maps of topological spaces is stable under composition, the induced
morphism property of schemes is stable under composition. -/
lemma topologically_isStableUnderComposition
    (hP : ∀ {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α → β) (g : β → γ) (_ : P f) (_ : P g), P (g ∘ f)) :
    (topologically P).IsStableUnderComposition where
  comp_mem {X Y Z} f g hf hg := by
    simp only [topologically, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact hP _ _ hf hg

/-- If a property of maps of topological spaces is satisfied by all homeomorphisms,
every isomorphism of schemes satisfies the induced property. -/
lemma topologically_iso_le
    (hP : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f) :
    MorphismProperty.isomorphisms Scheme ≤ (topologically P) := by
  intro X Y e (he : IsIso e)
  exact hP (TopCat.homeoOfIso (asIso e.base))

/-- If a property of maps of topological spaces is satisfied by homeomorphisms and is stable
under composition, the induced property on schemes respects isomorphisms. -/
lemma topologically_respectsIso
    (hP₁ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α ≃ₜ β), P f)
    (hP₂ : ∀ {α β γ : Type u} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
      (f : α → β) (g : β → γ) (_ : P f) (_ : P g), P (g ∘ f)) :
      (topologically P).RespectsIso :=
  have : (topologically P).IsStableUnderComposition :=
    topologically_isStableUnderComposition P hP₂
  MorphismProperty.respectsIso_of_isStableUnderComposition (topologically_iso_le P hP₁)

/-- To check that a topologically defined morphism property is local at the target,
we may check the corresponding properties on topological spaces. -/
lemma topologically_isZariskiLocalAtTarget [(topologically P).RespectsIso]
    (hP₂ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) (s : Set β)
      (_ : Continuous f) (_ : IsOpen s), P f → P (s.restrictPreimage f))
    (hP₃ : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) {ι : Type u}
      (U : ι → Opens β) (_ : IsOpenCover U) (_ : Continuous f),
      (∀ i, P ((U i).carrier.restrictPreimage f)) → P f) :
    IsZariskiLocalAtTarget (topologically P) := by
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf
    simp_rw [topologically, morphismRestrict_base]
    exact hP₂ f U.carrier f.continuous U.2 hf
  · intro X Y f ι U hU hf
    apply hP₃ f U hU f.continuous fun i ↦ ?_
    rw [← morphismRestrict_base]
    exact hf i

/-- A variant of `topologically_isZariskiLocalAtTarget`
that takes one iff statement instead of two implications. -/
lemma topologically_isZariskiLocalAtTarget' [(topologically P).RespectsIso]
    (hP : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β) {ι : Type u}
      (U : ι → Opens β) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (∀ i, P ((U i).carrier.restrictPreimage f))) :
    IsZariskiLocalAtTarget (topologically P) := by
  refine topologically_isZariskiLocalAtTarget P ?_ (fun f _ U hU hU' ↦ (hP f U hU hU').mpr)
  introv hf hs H
  refine (hP f (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ?_ hf).mp H ⟨1⟩
  rw [IsOpenCover, ← top_le_iff]
  exact le_iSup (![⊤, Opens.mk s hs] ∘ Equiv.ulift) ⟨0⟩

lemma topologically_isZariskiLocalAtSource [(topologically P).RespectsIso]
    (hP₁ : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
      (_ : Continuous f) (U : Opens X), P f → P (f ∘ ((↑) : U → X)))
    (hP₂ : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y)
      (_ : Continuous f) {ι : Type u} (U : ι → Opens X),
      IsOpenCover U → (∀ i, P (f ∘ ((↑) : U i → X))) → P f) :
    IsZariskiLocalAtSource (topologically P) := by
  apply IsZariskiLocalAtSource.mk'
  · introv hf
    exact hP₁ f f.continuous _ hf
  · introv hU hf
    exact hP₂ f f.continuous _ hU hf

/-- A variant of `topologically_isZariskiLocalAtSource`
that takes one iff statement instead of two implications. -/
lemma topologically_isZariskiLocalAtSource' [(topologically P).RespectsIso]
    (hP : ∀ {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y) {ι : Type u}
      (U : ι → Opens X) (_ : IsOpenCover U) (_ : Continuous f),
      P f ↔ (∀ i, P (f ∘ ((↑) : U i → X)))) :
    IsZariskiLocalAtSource (topologically P) := by
  refine topologically_isZariskiLocalAtSource P ?_ (fun f hf _ U hU hf' ↦ (hP f U hU hf).mpr hf')
  introv hf hs
  refine (hP f (![⊤, U] ∘ Equiv.ulift) ?_ hf).mp hs ⟨1⟩
  rw [IsOpenCover, ← top_le_iff]
  exact le_iSup (![⊤, U] ∘ Equiv.ulift) ⟨0⟩

end Topologically

/-- `stalkwise P` holds for a morphism if all stalks satisfy `P`. -/
def stalkwise (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop) :
    MorphismProperty Scheme.{u} :=
  fun _ _ f => ∀ x, P (f.stalkMap x).hom

section Stalkwise

variable {P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop}

/-- If `P` respects isos, then `stalkwise P` respects isos. -/
lemma stalkwise_respectsIso (hP : RingHom.RespectsIso P) :
    (stalkwise P).RespectsIso where
  precomp {X Y Z} e (he : IsIso e) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.RespectsIso.cancel_right_isIso hP _ _).mpr <| hf (e x)
  postcomp {X Y Z} e (he : IsIso _) f hf := by
    simp only [stalkwise, Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply]
    intro x
    rw [Scheme.Hom.stalkMap_comp]
    exact (RingHom.RespectsIso.cancel_left_isIso hP _ _).mpr <| hf x

/-- If `P` respects isos, then `stalkwise P` is local at the target. -/
lemma stalkwiseIsZariskiLocalAtTarget_of_respectsIso (hP : RingHom.RespectsIso P) :
    IsZariskiLocalAtTarget (stalkwise P) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  letI := stalkwise_respectsIso hP
  apply IsZariskiLocalAtTarget.mk'
  · intro X Y f U hf x
    apply ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f U x).mpr <| hf _
  · intro X Y f ι U hU hf x
    have hy : f x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    exact ((RingHom.toMorphismProperty P).arrow_mk_iso_iff <|
      morphismRestrictStalkMap f (U i) ⟨x, hi⟩).mp <| hf i ⟨x, hi⟩

set_option backward.isDefEq.respectTransparency false in
/-- If `P` respects isos, then `stalkwise P` is local at the source. -/
lemma stalkwise_isZariskiLocalAtSource_of_respectsIso (hP : RingHom.RespectsIso P) :
    IsZariskiLocalAtSource (stalkwise P) := by
  letI := stalkwise_respectsIso hP
  apply IsZariskiLocalAtSource.mk'
  · intro X Y f U hf x
    rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp, hP.cancel_right_isIso]
    exact hf _
  · intro X Y f ι U hU hf x
    have hy : x ∈ iSup U := by rw [hU]; trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    rw [← hP.cancel_right_isIso _ ((U i).ι.stalkMap ⟨x, hi⟩)]
    simpa [Scheme.Hom.stalkMap_comp] using hf i ⟨x, hi⟩

lemma stalkwise_SpecMap_iff (hP : RingHom.RespectsIso P) {R S : CommRingCat} (φ : R ⟶ S) :
    stalkwise P (Spec.map φ) ↔ ∀ (p : Ideal S) (_ : p.IsPrime),
      P (Localization.localRingHom _ p φ.hom rfl) := by
  have hP' : (RingHom.toMorphismProperty P).RespectsIso :=
    RingHom.toMorphismProperty_respectsIso_iff.mp hP
  trans ∀ (p : PrimeSpectrum S), P (Localization.localRingHom _ p.asIdeal φ.hom rfl)
  · exact forall_congr' fun p ↦
      (RingHom.toMorphismProperty P).arrow_mk_iso_iff (Scheme.arrowStalkMapSpecIso _ _)
  · exact ⟨fun H p hp ↦ H ⟨p, hp⟩, fun H p ↦ H p.1 p.2⟩

end Stalkwise

namespace AffineTargetMorphismProperty

/-- If `P` is local at the target, to show that `P` is stable under base change, it suffices to
check this for base change along a morphism of affine schemes. -/
lemma isStableUnderBaseChange_of_isStableUnderBaseChangeOnAffine_of_isZariskiLocalAtTarget
    (P : MorphismProperty Scheme) [IsZariskiLocalAtTarget P]
    (hP₂ : (of P).IsStableUnderBaseChange) :
    P.IsStableUnderBaseChange :=
  letI := HasAffineProperty.of_isZariskiLocalAtTarget P
  HasAffineProperty.isStableUnderBaseChange hP₂

end AffineTargetMorphismProperty

end AlgebraicGeometry

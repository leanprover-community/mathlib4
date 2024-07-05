/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty.Limits
import Mathlib.Data.List.TFAE

#align_import algebraic_geometry.morphisms.basic from "leanprover-community/mathlib"@"434e2fd21c1900747afc6d13d8be7f4eedba7218"

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `MorphismProperty Scheme` is a predicate on morphisms between schemes, and an
`AffineTargetMorphismProperty` is a predicate on morphisms into affine schemes. Given a
`P : AffineTargetMorphismProperty`, we may construct a `MorphismProperty` called
`targetAffineLocally P` that holds for `f : X ⟶ Y` whenever `P` holds for the
restriction of `f` on every affine open subset of `Y`.

## Main definitions

- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal`: We say that `P.IsLocal` if `P`
satisfies the assumptions of the affine communication lemma
(`AlgebraicGeometry.of_affine_open_cover`). That is,
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.

- `AlgebraicGeometry.PropertyIsLocalAtTarget`: We say that `PropertyIsLocalAtTarget P` for
`P : MorphismProperty Scheme` if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.

## Main results

- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_TFAE`:
  If `P.IsLocal`, then `targetAffineLocally P f` iff there exists an affine cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.
- `AlgebraicGeometry.AffineTargetMorphismProperty.isLocalOfOpenCoverImply`:
  If the existence of an affine cover `{ Uᵢ }` of `Y` such that `P` holds for `f ∣_ Uᵢ` implies
  `targetAffineLocally P f`, then `P.IsLocal`.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_target_iff`:
  If `Y` is affine and `f : X ⟶ Y`, then `targetAffineLocally P f ↔ P f` provided `P.IsLocal`.
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocally_isLocal` :
  If `P.IsLocal`, then `PropertyIsLocalAtTarget (targetAffineLocally P)`.
- `AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_TFAE`:
  If `PropertyIsLocalAtTarget P`, then `P f` iff there exists an open cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.

These results should not be used directly, and should be ported to each property that is local.

-/

set_option linter.uppercaseLean3 false

universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- An `AffineTargetMorphismProperty` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (_ : X ⟶ Y) [IsAffine Y], Prop
#align algebraic_geometry.affine_target_morphism_property AlgebraicGeometry.AffineTargetMorphismProperty

/-- `IsIso` as a `MorphismProperty`. -/
protected def Scheme.isIso : MorphismProperty Scheme :=
  @IsIso Scheme _
#align algebraic_geometry.Scheme.is_iso AlgebraicGeometry.Scheme.isIso

/-- `IsIso` as an `AffineTargetMorphismProperty`. -/
protected def Scheme.affineTargetIsIso : AffineTargetMorphismProperty := fun _ _ f _ => IsIso f
#align algebraic_geometry.Scheme.affine_target_is_iso AlgebraicGeometry.Scheme.affineTargetIsIso

instance : Inhabited AffineTargetMorphismProperty := ⟨Scheme.affineTargetIsIso⟩

/-- An `AffineTargetMorphismProperty` can be extended to a `MorphismProperty` such that it
*never* holds when the target is not affine -/
def AffineTargetMorphismProperty.toProperty (P : AffineTargetMorphismProperty) :
    MorphismProperty Scheme := fun _ _ f => ∃ h, @P _ _ f h
#align algebraic_geometry.affine_target_morphism_property.to_property AlgebraicGeometry.AffineTargetMorphismProperty.toProperty

theorem AffineTargetMorphismProperty.toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [i : IsAffine Y] : P.toProperty f ↔ P f := by
  delta AffineTargetMorphismProperty.toProperty; simp [*]
#align algebraic_geometry.affine_target_morphism_property.to_property_apply AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply

theorem AffineTargetMorphismProperty.cancel_left_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, P.toProperty.cancel_left_of_respectsIso]
#align algebraic_geometry.affine_cancel_left_is_iso AlgebraicGeometry.AffineTargetMorphismProperty.cancel_left_of_respectsIso

theorem AffineTargetMorphismProperty.cancel_right_of_respectsIso
    (P : AffineTargetMorphismProperty) [P.toProperty.RespectsIso]
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply,
      P.toProperty.cancel_right_of_respectsIso]
#align algebraic_geometry.affine_cancel_right_is_iso AlgebraicGeometry.AffineTargetMorphismProperty.cancel_right_of_respectsIso

@[deprecated (since := "2024-07-02")] alias affine_cancel_left_isIso :=
  AffineTargetMorphismProperty.cancel_left_of_respectsIso
@[deprecated (since := "2024-07-02")] alias affine_cancel_right_isIso :=
  AffineTargetMorphismProperty.cancel_right_of_respectsIso

theorem AffineTargetMorphismProperty.respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [h : IsAffine Y],
      P f → @P _ _ (f ≫ e.hom) (isAffine_of_isIso e.inv)) :
    P.toProperty.RespectsIso := by
  constructor
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨isAffine_of_isIso e.inv, h₂ e f h⟩
#align algebraic_geometry.affine_target_morphism_property.respects_iso_mk AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk

/-- For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, P (f ∣_ U)
#align algebraic_geometry.target_affine_locally AlgebraicGeometry.targetAffineLocally

theorem IsAffineOpen.preimage_of_isIso {X Y : Scheme} {U : Opens Y.carrier} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsIso f] : IsAffineOpen (f ⁻¹ᵁ U) :=
  haveI : IsAffine _ := hU
  isAffine_of_isIso (f ∣_ U)
#align algebraic_geometry.is_affine_open.map_is_iso AlgebraicGeometry.IsAffineOpen.preimage_of_isIso

instance targetAffineLocally_respectsIso (P : AffineTargetMorphismProperty)
    [P.toProperty.RespectsIso] : (targetAffineLocally P).RespectsIso := by
  constructor
  · introv H U
    rw [morphismRestrict_comp, P.cancel_left_of_respectsIso]
    exact H U
  · introv H
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    haveI : IsAffine _ := hU.preimage_of_isIso e.hom
    rw [morphismRestrict_comp, P.cancel_right_of_respectsIso]
    exact H ⟨(Opens.map e.hom.val.base).obj U, hU.preimage_of_isIso e.hom⟩
#align algebraic_geometry.target_affine_locally_respects_iso AlgebraicGeometry.targetAffineLocally_respectsIso

/-- We say that `P : AffineTargetMorphismProperty` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basicOpen r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basicOpen r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.
-/
structure AffineTargetMorphismProperty.IsLocal (P : AffineTargetMorphismProperty) : Prop where
  /-- `P` as a morphism property respects isomorphisms -/
  RespectsIso : P.toProperty.RespectsIso
  /-- `P` is stable under restriction to basic open set of global sections. -/
  toBasicOpen :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Γ(Y, ⊤)),
      P f → @P _ _ (f ∣_ Y.basicOpen r) ((isAffineOpen_top Y).basicOpen _)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
    sections -/
  ofBasicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset Γ(Y, ⊤))
      (_ : Ideal.span (s : Set Γ(Y, ⊤)) = ⊤),
      (∀ r : s, @P _ _ (f ∣_ Y.basicOpen r.1) ((isAffineOpen_top Y).basicOpen _)) → P f
#align algebraic_geometry.affine_target_morphism_property.is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal

/-- Specialization of `ConcreteCategory.id_apply` because `simp` can't see through the defeq. -/
@[local simp] lemma CommRingCat.id_apply (R : CommRingCat) (x : R) : 𝟙 R x = x := rfl

theorem targetAffineLocally_of_openCover {P : AffineTargetMorphismProperty} (hP : P.IsLocal)
    {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)]
    (h𝒰 : ∀ i, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) :
    targetAffineLocally P f := by
  have := hP.1
  classical
  let S i : Y.affineOpens := ⟨_, isAffineOpen_opensRange (𝒰.map i)⟩
  intro U
  induction U using of_affine_open_cover S 𝒰.iSup_opensRange with
  | basicOpen U r h =>
    haveI : IsAffine _ := U.2
    have := hP.2 (f ∣_ U.1)
    replace this := this (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op r) h
    rw [← P.toProperty_apply] at this ⊢
    exact (P.toProperty.arrow_mk_iso_iff (morphismRestrictRestrictBasicOpen f _ r)).mp this
  | openCover U s hs H =>
    haveI : IsAffine _ := U.2
    apply hP.3 (f ∣_ U.1) (s.image (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op))
    · apply_fun Ideal.comap (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top.symm).op) at hs
      rw [Ideal.comap_top] at hs
      rw [← hs]
      simp only [eqToHom_op, eqToHom_map, Finset.coe_image]
      have : ∀ {R S : CommRingCat} (e : S = R) (s : Set S),
          Ideal.span (eqToHom e '' s) = Ideal.comap (eqToHom e.symm) (Ideal.span s) := by
        intro _ S e _
        subst e
        simp only [eqToHom_refl, CommRingCat.id_apply, Set.image_id']
        -- Porting note: Lean didn't see `𝟙 _` is just ring hom id
        exact (Ideal.comap_id _).symm
      apply this
    · rintro ⟨r, hr⟩
      obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
      specialize H ⟨r, hr'⟩
      rw [← P.toProperty_apply] at H ⊢
      exact (P.toProperty.arrow_mk_iso_iff (morphismRestrictRestrictBasicOpen f _ r)).mpr H
  | hU i =>
    specialize h𝒰 i
    rw [← P.toProperty_apply] at h𝒰 ⊢
    exact (P.toProperty.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr h𝒰
#align algebraic_geometry.target_affine_locally_of_open_cover AlgebraicGeometry.targetAffineLocally_of_openCover

open List in
theorem AffineTargetMorphismProperty.IsLocal.affine_openCover_TFAE
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [targetAffineLocally P f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g],
          P (pullback.snd : pullback f g ⟶ U),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (_ : iSup U = ⊤) (hU' : ∀ i, IsAffineOpen (U i)),
          ∀ i, @P _ _ (f ∣_ U i) (hU' i)] := by
  have := hP.1
  tfae_have 1 → 4
  · intro H U g h₁ h₂
    replace H := H ⟨_, isAffineOpen_opensRange g⟩
    rw [← P.toProperty_apply] at H ⊢
    rwa [← P.toProperty.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
  tfae_have 4 → 3
  · intro H 𝒰 h𝒰 i
    apply H
  tfae_have 3 → 2
  · exact fun H => ⟨Y.affineCover, inferInstance, H Y.affineCover⟩
  tfae_have 2 → 1
  · rintro ⟨𝒰, h𝒰, H⟩; exact targetAffineLocally_of_openCover hP f 𝒰 H
  tfae_have 5 → 2
  · rintro ⟨ι, U, hU, hU', H⟩
    refine ⟨Y.openCoverOfSuprEqTop U hU, hU', ?_⟩
    intro i
    specialize H i
    rw [← P.toProperty_apply, ← P.toProperty.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    rw [← P.toProperty_apply] at H
    convert H
    all_goals ext1; exact Subtype.range_coe
  tfae_have 1 → 5
  · intro H
    refine ⟨Y.carrier, fun x => (Scheme.Hom.opensRange <| Y.affineCover.map x),
      ?_, fun i => isAffineOpen_opensRange _, ?_⟩
    · rw [eq_top_iff]; intro x _; erw [Opens.mem_iSup]; exact ⟨x, Y.affineCover.covers x⟩
    · intro i; exact H ⟨_, isAffineOpen_opensRange _⟩
  tfae_finish
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_tfae AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_TFAE

theorem AffineTargetMorphismProperty.isLocalOfOpenCoverImply (P : AffineTargetMorphismProperty)
    [P.toProperty.RespectsIso]
    (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
        ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) →
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g],
          P (pullback.snd : pullback f g ⟶ U)) :
    P.IsLocal := by
  refine ⟨by assumption, ?_, ?_⟩
  · introv h
    haveI : IsAffine _ := (isAffineOpen_top Y).basicOpen r
    delta morphismRestrict
    rw [P.cancel_left_of_respectsIso]
    refine @H _ _ f ⟨Scheme.openCoverOfIsIso (𝟙 Y), ?_, ?_⟩ _ (Y.ofRestrict _) _ _
    · intro i; dsimp; infer_instance
    · intro i; dsimp
      rwa [← Category.comp_id pullback.snd, ← pullback.condition, P.cancel_left_of_respectsIso]
  · introv hs hs'
    replace hs := ((isAffineOpen_top Y).basicOpen_union_eq_self_iff _).mpr hs
    have := H f ⟨Y.openCoverOfSuprEqTop _ hs, ?_, ?_⟩ (𝟙 _)
    · rwa [← Category.comp_id pullback.snd, ← pullback.condition, P.cancel_left_of_respectsIso]
        at this
    · intro i; exact (isAffineOpen_top Y).basicOpen _
    · rintro (i : s)
      specialize hs' i
      haveI : IsAffine _ := (isAffineOpen_top Y).basicOpen i.1
      delta morphismRestrict at hs'
      rwa [P.cancel_left_of_respectsIso] at hs'
#align algebraic_geometry.affine_target_morphism_property.is_local_of_open_cover_imply AlgebraicGeometry.AffineTargetMorphismProperty.isLocalOfOpenCoverImply

theorem AffineTargetMorphismProperty.IsLocal.affine_openCover_iff {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y)
    [h𝒰 : ∀ i, IsAffine (𝒰.obj i)] :
    targetAffineLocally P f ↔ ∀ i, @P _ _ (pullback.snd : pullback f (𝒰.map i) ⟶ _) (h𝒰 i) := by
  refine ⟨fun H => let h := ((hP.affine_openCover_TFAE f).out 0 2).mp H; ?_,
    fun H => let h := ((hP.affine_openCover_TFAE f).out 1 0).mp; ?_⟩
  · exact fun i => h 𝒰 i
  · exact h ⟨𝒰, inferInstance, H⟩
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_iff AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_iff

theorem AffineTargetMorphismProperty.IsLocal.affine_target_iff {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    targetAffineLocally P f ↔ P f := by
  have := hP.1
  haveI : ∀ i, IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfIsIso (𝟙 Y)) i) := fun i => by
    dsimp; infer_instance
  rw [hP.affine_openCover_iff f (Scheme.openCoverOfIsIso (𝟙 Y))]
  trans P (pullback.snd : pullback f (𝟙 _) ⟶ _)
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← Category.comp_id pullback.snd, ← pullback.condition, P.cancel_left_of_respectsIso]
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_target_iff AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_target_iff

/-- We say that `P : MorphismProperty Scheme` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
structure PropertyIsLocalAtTarget (P : MorphismProperty Scheme) : Prop where
  /-- `P` respects isomorphisms. -/
  RespectsIso : P.RespectsIso
  /-- If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`. -/
  restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y), P f → P (f ∣_ U)
  /-- If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.  -/
  of_openCover :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
      (∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) → P f
#align algebraic_geometry.property_is_local_at_target AlgebraicGeometry.PropertyIsLocalAtTarget

lemma propertyIsLocalAtTarget_of_morphismRestrict (P : MorphismProperty Scheme)
    [P.RespectsIso]
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Opens Y), P f → P (f ∣_ U))
    (hP₃ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y)
      (_ : iSup U = ⊤), (∀ i, P (f ∣_ U i)) → P f) :
    PropertyIsLocalAtTarget P where
  RespectsIso := by assumption
  restrict := hP₂
  of_openCover {X Y} f 𝒰 h𝒰 := by
    apply hP₃ f (fun i : 𝒰.J => Scheme.Hom.opensRange (𝒰.map i)) 𝒰.iSup_opensRange
    simp_rw [P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    exact h𝒰

theorem AffineTargetMorphismProperty.IsLocal.targetAffineLocally_isLocal
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) :
    PropertyIsLocalAtTarget (targetAffineLocally P) := by
  have := hP.1
  constructor
  · infer_instance
  · intro X Y f U H V
    rw [← P.toProperty_apply (i := V.2),
      P.toProperty.arrow_mk_iso_iff (morphismRestrictRestrict f _ _)]
    convert H ⟨_, V.2.image_of_isOpenImmersion (Y.ofRestrict _)⟩
    rw [← P.toProperty_apply]
  · rintro X Y f 𝒰 h𝒰
    -- Porting note: rewrite `[(hP.affine_openCover_TFAE f).out 0 1` directly complains about
    -- metavariables
    have h01 := (hP.affine_openCover_TFAE f).out 0 1
    rw [h01]
    refine ⟨𝒰.bind fun _ => Scheme.affineCover _, ?_, ?_⟩
    · intro i; dsimp [Scheme.OpenCover.bind]; infer_instance
    · intro i
      specialize h𝒰 i.1
      -- Porting note: rewrite `[(hP.affine_openCover_TFAE pullback.snd).out 0 1` directly
      -- complains about metavariables
      have h02 := (hP.affine_openCover_TFAE (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)).out 0 2
      rw [h02] at h𝒰
      specialize h𝒰 (Scheme.affineCover _) i.2
      let e : pullback f ((𝒰.obj i.fst).affineCover.map i.snd ≫ 𝒰.map i.fst) ⟶
          pullback (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)
            ((𝒰.obj i.fst).affineCover.map i.snd) := by
        refine (pullbackSymmetry _ _).hom ≫ ?_
        refine (pullbackRightPullbackFstIso _ _ _).inv ≫ ?_
        refine (pullbackSymmetry _ _).hom ≫ ?_
        refine pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) ?_ ?_ <;>
        simp only [Category.comp_id, Category.id_comp, pullbackSymmetry_hom_comp_snd]
      rw [← P.cancel_left_of_respectsIso e] at h𝒰
      convert h𝒰 using 1
      simp [e]
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocally_isLocal

open List in
theorem PropertyIsLocalAtTarget.openCover_TFAE {P : MorphismProperty Scheme}
    (hP : PropertyIsLocalAtTarget P) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [P f,
        ∃ 𝒰 : Scheme.OpenCover.{u} Y,
          ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J),
          P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, P (f ∣_ U),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersion g], P (pullback.snd : pullback f g ⟶ U),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (_ : iSup U = ⊤), ∀ i, P (f ∣_ U i)] := by
  have := hP.1
  tfae_have 2 → 1
  · rintro ⟨𝒰, H⟩; exact hP.3 f 𝒰 H
  tfae_have 1 → 4
  · intro H U; exact hP.2 f U H
  tfae_have 4 → 3
  · intro H 𝒰 i
    rw [← P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    exact H <| Scheme.Hom.opensRange (𝒰.map i)
  tfae_have 3 → 2
  · exact fun H => ⟨Y.affineCover, H Y.affineCover⟩
  tfae_have 4 → 5
  · intro H U g hg
    rw [← P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    apply H
  tfae_have 5 → 4
  · intro H U
    erw [P.cancel_left_of_respectsIso]
    apply H
  tfae_have 4 → 6
  · intro H; exact ⟨PUnit, fun _ => ⊤, ciSup_const, fun _ => H _⟩
  tfae_have 6 → 2
  · rintro ⟨ι, U, hU, H⟩
    refine ⟨Y.openCoverOfSuprEqTop U hU, ?_⟩
    intro i
    rw [← P.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    convert H i
    all_goals ext1; exact Subtype.range_coe
  tfae_finish
#align algebraic_geometry.property_is_local_at_target.open_cover_tfae AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_TFAE

theorem PropertyIsLocalAtTarget.openCover_iff {P : MorphismProperty Scheme}
    (hP : PropertyIsLocalAtTarget P) {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) :
    P f ↔ ∀ i, P (pullback.snd : pullback f (𝒰.map i) ⟶ _) := by
  -- Porting note: couldn't get the term mode proof work
  refine ⟨fun H => let h := ((hP.openCover_TFAE f).out 0 2).mp H; fun i => ?_,
    fun H => let h := ((hP.openCover_TFAE f).out 1 0).mp; ?_⟩
  · exact h 𝒰 i
  · exact h ⟨𝒰, H⟩
#align algebraic_geometry.property_is_local_at_target.open_cover_iff AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_iff

namespace AffineTargetMorphismProperty

/-- A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
def StableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
    P g → P (pullback.fst : pullback f g ⟶ X)
#align algebraic_geometry.affine_target_morphism_property.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.StableUnderBaseChange

theorem IsLocal.targetAffineLocally_pullback_fst_of_right_of_stableUnderBaseChange
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) (hP' : P.StableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : P g) :
    targetAffineLocally P (pullback.fst : pullback f g ⟶ X) := by
  have := hP.1
  -- Porting note: rewrite `(hP.affine_openCover_TFAE ...).out 0 1` doesn't work
  have h01 := (hP.affine_openCover_TFAE (pullback.fst : pullback f g ⟶ X)).out 0 1
  rw [h01]
  use X.affineCover, inferInstance
  intro i
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.map i)
  have : e.hom ≫ pullback.fst = pullback.snd := by simp [e]
  rw [← this, P.cancel_left_of_respectsIso]
  apply hP'; assumption
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_pullback_fst_of_right_of_stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocally_pullback_fst_of_right_of_stableUnderBaseChange

theorem IsLocal.stableUnderBaseChange {P : AffineTargetMorphismProperty} (hP : P.IsLocal)
    (hP' : P.StableUnderBaseChange) : (targetAffineLocally P).StableUnderBaseChange :=
  have := hP.1
  MorphismProperty.StableUnderBaseChange.mk
    (fun X Y S f g H => by
      -- Porting note: rewrite `(...openCover_TFAE).out 0 1` directly doesn't work, complains about
      -- metavariable
      have h01 := (hP.targetAffineLocally_isLocal.openCover_TFAE
        (pullback.fst : pullback f g ⟶ X)).out 0 1
      rw [h01]
      use S.affineCover.pullbackCover f
      intro i
      -- Porting note: rewrite `(hP.affine_openCover_TFAE g).out 0 3` directly doesn't work
      -- complains about metavariable
      have h03 := (hP.affine_openCover_TFAE g).out 0 3
      rw [h03] at H
      let e : pullback (pullback.fst : pullback f g ⟶ _) ((S.affineCover.pullbackCover f).map i) ≅
          _ := by
        refine pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ ?_ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.map i) g
            (pullback.snd : pullback f (S.affineCover.map i) ⟶ _)).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst = pullback.snd := by simp [e]
      rw [← this, (targetAffineLocally P).cancel_left_of_respectsIso]
      apply hP.targetAffineLocally_pullback_fst_of_right_of_stableUnderBaseChange hP'
      rw [← pullbackSymmetry_hom_comp_snd, P.cancel_left_of_respectsIso]
      apply H)
#align algebraic_geometry.affine_target_morphism_property.is_local.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.stableUnderBaseChange

end AffineTargetMorphismProperty

namespace AffineTargetMorphismProperty.IsLocal

@[deprecated (since := "2024-06-22")]
alias targetAffineLocallyIsLocal := targetAffineLocally_isLocal

@[deprecated (since := "2024-06-22")]
alias targetAffineLocallyPullbackFstOfRightOfStableUnderBaseChange :=
  targetAffineLocally_pullback_fst_of_right_of_stableUnderBaseChange

end AffineTargetMorphismProperty.IsLocal

end AlgebraicGeometry

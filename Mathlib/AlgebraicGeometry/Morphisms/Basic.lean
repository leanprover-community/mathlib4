/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty
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
- `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocallyIsLocal` :
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
  -- ⊢ (∃ h, P f) ↔ P f
                                                 -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.to_property_apply AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply

theorem affine_cancel_left_isIso {P : AffineTargetMorphismProperty} (hP : P.toProperty.RespectsIso)
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.toProperty_apply, ← P.toProperty_apply, hP.cancel_left_isIso]
  -- 🎉 no goals
#align algebraic_geometry.affine_cancel_left_is_iso AlgebraicGeometry.affine_cancel_left_isIso

theorem affine_cancel_right_isIso {P : AffineTargetMorphismProperty} (hP : P.toProperty.RespectsIso)
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.toProperty_apply, ← P.toProperty_apply, hP.cancel_right_isIso]
                          -- 🎉 no goals
#align algebraic_geometry.affine_cancel_right_is_iso AlgebraicGeometry.affine_cancel_right_isIso

theorem AffineTargetMorphismProperty.respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ : ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [h : IsAffine Y],
      P f → @P _ _ (f ≫ e.hom) (isAffineOfIso e.inv)) :
    P.toProperty.RespectsIso := by
  constructor
  -- ⊢ ∀ {X Y Z : Scheme} (e : X ≅ Y) (f : Y ⟶ Z), toProperty P f → toProperty P (e …
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
    -- ⊢ toProperty P (e.hom ≫ f)
                             -- 🎉 no goals
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨isAffineOfIso e.inv, h₂ e f h⟩
    -- ⊢ toProperty P (f ≫ e.hom)
                             -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.respects_iso_mk AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk

/-- For a `P : AffineTargetMorphismProperty`, `targetAffineLocally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, @P _ _ (f ∣_ U) U.prop
#align algebraic_geometry.target_affine_locally AlgebraicGeometry.targetAffineLocally

theorem IsAffineOpen.map_isIso {X Y : Scheme} {U : Opens Y.carrier} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsIso f] : IsAffineOpen ((Opens.map f.1.base).obj U) :=
  haveI : IsAffine _ := hU
  isAffineOfIso (f ∣_ U)
#align algebraic_geometry.is_affine_open.map_is_iso AlgebraicGeometry.IsAffineOpen.map_isIso

theorem targetAffineLocally_respectsIso {P : AffineTargetMorphismProperty}
    (hP : P.toProperty.RespectsIso) : (targetAffineLocally P).RespectsIso := by
  constructor
  -- ⊢ ∀ {X Y Z : Scheme} (e : X ≅ Y) (f : Y ⟶ Z), targetAffineLocally P f → target …
  · introv H U
    -- ⊢ P ((e.hom ≫ f) ∣_ ↑U)
    -- Porting note : added this instance
    haveI : IsAffine _ := U.prop
    -- ⊢ P ((e.hom ≫ f) ∣_ ↑U)
    rw [morphismRestrict_comp, affine_cancel_left_isIso hP]
    -- ⊢ P (f ∣_ ↑U)
    exact H U
    -- 🎉 no goals
  · introv H
    -- ⊢ targetAffineLocally P (f ≫ e.hom)
    rintro ⟨U, hU : IsAffineOpen U⟩; dsimp
    -- ⊢ P ((f ≫ e.hom) ∣_ ↑{ val := U, property := hU })
                                     -- ⊢ P ((f ≫ e.hom) ∣_ U)
    haveI : IsAffine _ := hU
    -- ⊢ P ((f ≫ e.hom) ∣_ U)
    haveI : IsAffine _ := hU.map_isIso e.hom
    -- ⊢ P ((f ≫ e.hom) ∣_ U)
    rw [morphismRestrict_comp, affine_cancel_right_isIso hP]
    -- ⊢ P (f ∣_ (Opens.map e.hom.val.base).obj U)
    exact H ⟨(Opens.map e.hom.val.base).obj U, hU.map_isIso e.hom⟩
    -- 🎉 no goals
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
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Y.presheaf.obj <| op ⊤),
      P f → @P _ _ (f ∣_ Y.basicOpen r) ((topIsAffineOpen Y).basicOpenIsAffine _)
  /-- `P` for `f` if `P` holds for `f` restricted to basic sets of a spanning set of the global
    sections -/
  ofBasicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset (Y.presheaf.obj <| op ⊤))
      (_ : Ideal.span (s : Set (Y.presheaf.obj <| op ⊤)) = ⊤),
      (∀ r : s, @P _ _ (f ∣_ Y.basicOpen r.1) ((topIsAffineOpen Y).basicOpenIsAffine _)) → P f
#align algebraic_geometry.affine_target_morphism_property.is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal

theorem targetAffineLocallyOfOpenCover {P : AffineTargetMorphismProperty} (hP : P.IsLocal)
    {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)]
    (h𝒰 : ∀ i, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) :
    targetAffineLocally P f := by
  classical
  let S i := (⟨⟨Set.range (𝒰.map i).1.base, (𝒰.IsOpen i).base_open.open_range⟩,
    rangeIsAffineOpenOfOpenImmersion (𝒰.map i)⟩ : Y.affineOpens)
  intro U
  apply of_affine_open_cover (P := _) U (Set.range S)
  · intro U r h
    haveI : IsAffine _ := U.2
    have := hP.2 (f ∣_ U.1)
    replace this := this (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op r) h
    -- Porting note : the following 2 instances was not necessary
    haveI i1 : IsAffine (Y.restrict (Scheme.affineBasicOpen Y r).1.openEmbedding) :=
      (Scheme.affineBasicOpen Y r).2
    haveI i2 : IsAffine
      ((Y.restrict U.1.openEmbedding).restrict
        ((Y.restrict U.1.openEmbedding).basicOpen <|
          (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op r)).openEmbedding) :=
      IsAffineOpen.basicOpenIsAffine (X := Y.restrict U.1.openEmbedding) (topIsAffineOpen _) _
    rw [← P.toProperty_apply] at this ⊢
    exact (hP.1.arrow_mk_iso_iff (morphismRestrictRestrictBasicOpen f _ r)).mp this
  · intro U s hs H
    haveI : IsAffine _ := U.2
    apply hP.3 (f ∣_ U.1) (s.image (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op))
    · apply_fun Ideal.comap (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top.symm).op) at hs
      rw [Ideal.comap_top] at hs
      rw [← hs]
      simp only [eqToHom_op, eqToHom_map, Finset.coe_image]
      have : ∀ {R S : CommRingCat} (e : S = R) (s : Set S),
          Ideal.span (eqToHom e '' s) = Ideal.comap (eqToHom e.symm) (Ideal.span s) := by
        intro _ _ e _
        subst e
        simp only [eqToHom_refl, id_apply, Set.image_id']
        -- Porting note : Lean didn't see `𝟙 _` is just ring hom id
        exact (Ideal.comap_id _).symm
      apply this
    · rintro ⟨r, hr⟩
      obtain ⟨r, hr', rfl⟩ := Finset.mem_image.mp hr
      specialize H ⟨r, hr'⟩
      -- Porting note : the following 2 instances was not necessary
      haveI i1 : IsAffine (Y.restrict (Scheme.affineBasicOpen Y r).1.openEmbedding) :=
        (Scheme.affineBasicOpen Y r).2
      haveI i2 : IsAffine
        ((Y.restrict U.1.openEmbedding).restrict
          ((Y.restrict U.1.openEmbedding).basicOpen <|
            (Y.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op r)).openEmbedding) :=
        IsAffineOpen.basicOpenIsAffine (X := Y.restrict U.1.openEmbedding) (topIsAffineOpen _) _
      rw [← P.toProperty_apply] at H ⊢
      exact (hP.1.arrow_mk_iso_iff (morphismRestrictRestrictBasicOpen f _ r)).mpr H
  · rw [Set.eq_univ_iff_forall]
    simp only [Set.mem_iUnion]
    intro x
    exact ⟨⟨_, ⟨𝒰.f x, rfl⟩⟩, 𝒰.Covers x⟩
  · rintro ⟨_, i, rfl⟩
    specialize h𝒰 i
    -- Porting note : the next instance was not necessary
    haveI i1 : IsAffine (Y.restrict (S i).1.openEmbedding) := (S i).2
    rw [← P.toProperty_apply] at h𝒰 ⊢
    exact (hP.1.arrow_mk_iso_iff (morphismRestrictOpensRange f _)).mpr h𝒰
#align algebraic_geometry.target_affine_locally_of_open_cover AlgebraicGeometry.targetAffineLocallyOfOpenCover

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
  tfae_have 1 → 4
  -- ⊢ targetAffineLocally P f → ∀ {U : Scheme} (g : U ⟶ Y) [inst : IsAffine U] [in …
  · intro H U g h₁ h₂
    -- ⊢ P pullback.snd
    -- Porting note : I need to add `i1` manually, so to save some typing, named this variable
    set U' : Opens _ := ⟨_, h₂.base_open.open_range⟩
    -- ⊢ P pullback.snd
    replace H := H ⟨U', rangeIsAffineOpenOfOpenImmersion g⟩
    -- ⊢ P pullback.snd
    haveI i1 : IsAffine (Y.restrict U'.openEmbedding) := rangeIsAffineOpenOfOpenImmersion g
    -- ⊢ P pullback.snd
    rw [← P.toProperty_apply] at H ⊢
    -- ⊢ toProperty P pullback.snd
    rwa [← hP.1.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    -- 🎉 no goals
  tfae_have 4 → 3
  -- ⊢ (∀ {U : Scheme} (g : U ⟶ Y) [inst : IsAffine U] [inst_1 : IsOpenImmersion g] …
  · intro H 𝒰 h𝒰 i
    -- ⊢ P pullback.snd
    apply H
    -- 🎉 no goals
  tfae_have 3 → 2
  -- ⊢ (∀ (𝒰 : Scheme.OpenCover Y) [inst : ∀ (i : 𝒰.J), IsAffine (Scheme.OpenCover. …
  · exact fun H => ⟨Y.affineCover, inferInstance, H Y.affineCover⟩
    -- 🎉 no goals
  tfae_have 2 → 1
  -- ⊢ (∃ 𝒰 x, ∀ (i : 𝒰.J), P pullback.snd) → targetAffineLocally P f
  · rintro ⟨𝒰, h𝒰, H⟩; exact targetAffineLocallyOfOpenCover hP f 𝒰 H
    -- ⊢ targetAffineLocally P f
                       -- 🎉 no goals
  tfae_have 5 → 2
  -- ⊢ (∃ ι U x hU', ∀ (i : ι), P (f ∣_ U i)) → ∃ 𝒰 x, ∀ (i : 𝒰.J), P pullback.snd
  · rintro ⟨ι, U, hU, hU', H⟩
    -- ⊢ ∃ 𝒰 x, ∀ (i : 𝒰.J), P pullback.snd
    refine' ⟨Y.openCoverOfSuprEqTop U hU, hU', _⟩
    -- ⊢ ∀ (i : (Scheme.openCoverOfSuprEqTop Y U hU).J), P pullback.snd
    intro i
    -- ⊢ P pullback.snd
    specialize H i
    -- ⊢ P pullback.snd
    -- Porting note : added these two instances manually
    haveI i2 : IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfSuprEqTop Y U hU) i) := hU' i
    -- ⊢ P pullback.snd
    haveI i3 : IsAffine (Y.restrict (U i).openEmbedding) := hU' i
    -- ⊢ P pullback.snd
    rw [← P.toProperty_apply, ← hP.1.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    -- ⊢ toProperty P (f ∣_ Scheme.Hom.opensRange (Scheme.OpenCover.map (Scheme.openC …
    rw [← P.toProperty_apply] at H
    -- ⊢ toProperty P (f ∣_ Scheme.Hom.opensRange (Scheme.OpenCover.map (Scheme.openC …
    convert H
    all_goals ext1; exact Subtype.range_coe
    -- 🎉 no goals
  tfae_have 1 → 5
  -- ⊢ targetAffineLocally P f → ∃ ι U x hU', ∀ (i : ι), P (f ∣_ U i)
  · intro H
    -- ⊢ ∃ ι U x hU', ∀ (i : ι), P (f ∣_ U i)
    refine ⟨Y.carrier, fun x => (Scheme.Hom.opensRange <| Y.affineCover.map x),
      ?_, fun i => rangeIsAffineOpenOfOpenImmersion _, ?_⟩
    · rw [eq_top_iff]; intro x _; erw [Opens.mem_iSup]; exact ⟨x, Y.affineCover.Covers x⟩
      -- ⊢ ⊤ ≤ ⨆ (x : ↑↑Y.toPresheafedSpace), Scheme.Hom.opensRange (Scheme.OpenCover.m …
                       -- ⊢ x ∈ ↑(⨆ (x : ↑↑Y.toPresheafedSpace), Scheme.Hom.opensRange (Scheme.OpenCover …
                                  -- ⊢ ∃ i, x ∈ Scheme.Hom.opensRange (Scheme.OpenCover.map (Scheme.affineCover Y) i)
                                                        -- 🎉 no goals
    · intro i; exact H ⟨_, rangeIsAffineOpenOfOpenImmersion _⟩
      -- ⊢ P (f ∣_ (fun x => Scheme.Hom.opensRange (Scheme.OpenCover.map (Scheme.affine …
               -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_tfae AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_TFAE

theorem AffineTargetMorphismProperty.isLocalOfOpenCoverImply (P : AffineTargetMorphismProperty)
    (hP : P.toProperty.RespectsIso)
    (H : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
      (∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
        ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) →
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersion g],
          P (pullback.snd : pullback f g ⟶ U)) :
    P.IsLocal := by
  refine' ⟨hP, _, _⟩
  -- ⊢ ∀ {X Y : Scheme} [inst : IsAffine Y] (f : X ⟶ Y) (r : ↑(Y.presheaf.obj (op ⊤ …
  · introv h
    -- ⊢ P (f ∣_ Scheme.basicOpen Y r)
    haveI : IsAffine _ := (topIsAffineOpen Y).basicOpenIsAffine r
    -- ⊢ P (f ∣_ Scheme.basicOpen Y r)
    delta morphismRestrict
    -- ⊢ P ((pullbackRestrictIsoRestrict f (Scheme.basicOpen Y r)).inv ≫ pullback.snd)
    rw [affine_cancel_left_isIso hP]
    -- ⊢ P pullback.snd
    refine' @H _ _ f ⟨Scheme.openCoverOfIsIso (𝟙 Y), _, _⟩ _ (Y.ofRestrict _) _ _
    -- ⊢ ∀ (i : (Scheme.openCoverOfIsIso (𝟙 Y)).J), IsAffine (Scheme.OpenCover.obj (S …
    · intro i; dsimp; infer_instance
      -- ⊢ IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfIsIso (𝟙 Y)) i)
               -- ⊢ IsAffine Y
                      -- 🎉 no goals
    · intro i; dsimp
      -- ⊢ P pullback.snd
               -- ⊢ P pullback.snd
      rwa [← Category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_isIso hP]
      -- 🎉 no goals
  · introv hs hs'
    -- ⊢ P f
    replace hs := ((topIsAffineOpen Y).basicOpen_union_eq_self_iff _).mpr hs
    -- ⊢ P f
    have := H f ⟨Y.openCoverOfSuprEqTop _ hs, ?_, ?_⟩ (𝟙 _)
    rwa [← Category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_isIso hP]
      at this
    · intro i; exact (topIsAffineOpen Y).basicOpenIsAffine _
      -- ⊢ IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfSuprEqTop Y (fun i => Sche …
               -- 🎉 no goals
    · rintro (i : s)
      -- ⊢ P pullback.snd
      specialize hs' i
      -- ⊢ P pullback.snd
      haveI : IsAffine _ := (topIsAffineOpen Y).basicOpenIsAffine i.1
      -- ⊢ P pullback.snd
      delta morphismRestrict at hs'
      -- ⊢ P pullback.snd
      rwa [affine_cancel_left_isIso hP] at hs'
      -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local_of_open_cover_imply AlgebraicGeometry.AffineTargetMorphismProperty.isLocalOfOpenCoverImply

theorem AffineTargetMorphismProperty.IsLocal.affine_openCover_iff {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y)
    [h𝒰 : ∀ i, IsAffine (𝒰.obj i)] :
    targetAffineLocally P f ↔ ∀ i, @P _ _ (pullback.snd : pullback f (𝒰.map i) ⟶ _) (h𝒰 i) := by
  refine' ⟨fun H => let h := ((hP.affine_openCover_TFAE f).out 0 2).mp H; _,
    fun H => let h := ((hP.affine_openCover_TFAE f).out 1 0).mp; _⟩
  · exact fun i => h 𝒰 i
    -- 🎉 no goals
  · exact h ⟨𝒰, inferInstance, H⟩
    -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_iff AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_iff

theorem AffineTargetMorphismProperty.IsLocal.affine_target_iff {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] :
    targetAffineLocally P f ↔ P f := by
  haveI : ∀ i, IsAffine (Scheme.OpenCover.obj (Scheme.openCoverOfIsIso (𝟙 Y)) i) := fun i => by
    dsimp; infer_instance
  rw [hP.affine_openCover_iff f (Scheme.openCoverOfIsIso (𝟙 Y))]
  -- ⊢ (∀ (i : (Scheme.openCoverOfIsIso (𝟙 Y)).J), P pullback.snd) ↔ P f
  trans P (pullback.snd : pullback f (𝟙 _) ⟶ _)
  -- ⊢ (∀ (i : (Scheme.openCoverOfIsIso (𝟙 Y)).J), P pullback.snd) ↔ P pullback.snd
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
    -- 🎉 no goals
  rw [← Category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_isIso hP.1]
  -- 🎉 no goals
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
  restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier), P f → P (f ∣_ U)
  /-- If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.  -/
  of_openCover :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
      (∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) → P f
#align algebraic_geometry.property_is_local_at_target AlgebraicGeometry.PropertyIsLocalAtTarget

theorem AffineTargetMorphismProperty.IsLocal.targetAffineLocallyIsLocal
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) :
    PropertyIsLocalAtTarget (targetAffineLocally P) := by
  constructor
  · exact targetAffineLocally_respectsIso hP.1
    -- 🎉 no goals
  · intro X Y f U H V
    -- ⊢ P (f ∣_ U ∣_ ↑V)
    rw [← P.toProperty_apply (i := V.2), hP.1.arrow_mk_iso_iff (morphismRestrictRestrict f _ _)]
    -- ⊢ toProperty P (f ∣_ (IsOpenMap.functor (_ : IsOpenMap ↑(Opens.inclusion U))). …
    convert H ⟨_, IsAffineOpen.imageIsOpenImmersion V.2 (Y.ofRestrict _)⟩
    -- ⊢ toProperty P (f ∣_ (IsOpenMap.functor (_ : IsOpenMap ↑(Opens.inclusion U))). …
    rw [← P.toProperty_apply (i := IsAffineOpen.imageIsOpenImmersion V.2 (Y.ofRestrict _))]
    -- 🎉 no goals
  · rintro X Y f 𝒰 h𝒰
    -- ⊢ targetAffineLocally P f
    -- Porting note : rewrite `[(hP.affine_openCover_TFAE f).out 0 1` directly complains about
    -- metavariables
    have h01 := (hP.affine_openCover_TFAE f).out 0 1
    -- ⊢ targetAffineLocally P f
    rw [h01]
    -- ⊢ ∃ 𝒰 x, ∀ (i : 𝒰.J), P pullback.snd
    refine' ⟨𝒰.bind fun _ => Scheme.affineCover _, _, _⟩
    -- ⊢ ∀ (i : (Scheme.OpenCover.bind 𝒰 fun x => Scheme.affineCover (Scheme.OpenCove …
    · intro i; dsimp [Scheme.OpenCover.bind]; infer_instance
      -- ⊢ IsAffine (Scheme.OpenCover.obj (Scheme.OpenCover.bind 𝒰 fun x => Scheme.affi …
               -- ⊢ IsAffine (Scheme.OpenCover.obj (Scheme.affineCover (Scheme.OpenCover.obj 𝒰 i …
                                              -- 🎉 no goals
    · intro i
      -- ⊢ P pullback.snd
      specialize h𝒰 i.1
      -- ⊢ P pullback.snd
      -- Porting note : rewrite `[(hP.affine_openCover_TFAE pullback.snd).out 0 1` directly
      -- complains about metavariables
      have h02 := (hP.affine_openCover_TFAE (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)).out 0 2
      -- ⊢ P pullback.snd
      rw [h02] at h𝒰
      -- ⊢ P pullback.snd
      specialize h𝒰 (Scheme.affineCover _) i.2
      -- ⊢ P pullback.snd
      let e : pullback f ((𝒰.obj i.fst).affineCover.map i.snd ≫ 𝒰.map i.fst) ⟶
          pullback (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)
            ((𝒰.obj i.fst).affineCover.map i.snd) := by
        refine' (pullbackSymmetry _ _).hom ≫ _
        refine' (pullbackRightPullbackFstIso _ _ _).inv ≫ _
        refine' (pullbackSymmetry _ _).hom ≫ _
        refine' pullback.map _ _ _ _ (pullbackSymmetry _ _).hom (𝟙 _) (𝟙 _) _ _ <;>
        simp only [Category.comp_id, Category.id_comp, pullbackSymmetry_hom_comp_snd]
      rw [← affine_cancel_left_isIso hP.1 e] at h𝒰
      -- ⊢ P pullback.snd
      convert h𝒰 using 1
      -- ⊢ pullback.snd = e ≫ pullback.snd
      simp
      -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocallyIsLocal

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
  tfae_have 2 → 1
  -- ⊢ (∃ 𝒰, ∀ (i : 𝒰.J), P pullback.snd) → P f
  · rintro ⟨𝒰, H⟩; exact hP.3 f 𝒰 H
    -- ⊢ P f
                   -- 🎉 no goals
  tfae_have 1 → 4
  -- ⊢ P f → ∀ (U : Opens ↑↑Y.toPresheafedSpace), P (f ∣_ U)
  · intro H U; exact hP.2 f U H
    -- ⊢ P (f ∣_ U)
               -- 🎉 no goals
  tfae_have 4 → 3
  -- ⊢ (∀ (U : Opens ↑↑Y.toPresheafedSpace), P (f ∣_ U)) → ∀ (𝒰 : Scheme.OpenCover  …
  · intro H 𝒰 i
    -- ⊢ P pullback.snd
    rw [← hP.1.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    -- ⊢ P (f ∣_ Scheme.Hom.opensRange (Scheme.OpenCover.map 𝒰 i))
    exact H <| Scheme.Hom.opensRange (𝒰.map i)
    -- 🎉 no goals
  tfae_have 3 → 2
  -- ⊢ (∀ (𝒰 : Scheme.OpenCover Y) (i : 𝒰.J), P pullback.snd) → ∃ 𝒰, ∀ (i : 𝒰.J), P …
  · exact fun H => ⟨Y.affineCover, H Y.affineCover⟩
    -- 🎉 no goals
  tfae_have 4 → 5
  -- ⊢ (∀ (U : Opens ↑↑Y.toPresheafedSpace), P (f ∣_ U)) → ∀ {U : Scheme} (g : U ⟶  …
  · intro H U g hg
    -- ⊢ P pullback.snd
    rw [← hP.1.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    -- ⊢ P (f ∣_ Scheme.Hom.opensRange g)
    apply H
    -- 🎉 no goals
  tfae_have 5 → 4
  -- ⊢ (∀ {U : Scheme} (g : U ⟶ Y) [inst : IsOpenImmersion g], P pullback.snd) → ∀  …
  · intro H U
    -- ⊢ P (f ∣_ U)
    erw [hP.1.cancel_left_isIso]
    -- ⊢ P pullback.snd
    apply H
    -- 🎉 no goals
  tfae_have 4 → 6
  -- ⊢ (∀ (U : Opens ↑↑Y.toPresheafedSpace), P (f ∣_ U)) → ∃ ι U x, ∀ (i : ι), P (f …
  · intro H; exact ⟨PUnit, fun _ => ⊤, ciSup_const, fun _ => H _⟩
    -- ⊢ ∃ ι U x, ∀ (i : ι), P (f ∣_ U i)
             -- 🎉 no goals
  tfae_have 6 → 2
  -- ⊢ (∃ ι U x, ∀ (i : ι), P (f ∣_ U i)) → ∃ 𝒰, ∀ (i : 𝒰.J), P pullback.snd
  · rintro ⟨ι, U, hU, H⟩
    -- ⊢ ∃ 𝒰, ∀ (i : 𝒰.J), P pullback.snd
    refine' ⟨Y.openCoverOfSuprEqTop U hU, _⟩
    -- ⊢ ∀ (i : (Scheme.openCoverOfSuprEqTop Y U hU).J), P pullback.snd
    intro i
    -- ⊢ P pullback.snd
    rw [← hP.1.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    -- ⊢ P (f ∣_ Scheme.Hom.opensRange (Scheme.OpenCover.map (Scheme.openCoverOfSuprE …
    convert H i
    all_goals ext1; exact Subtype.range_coe
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align algebraic_geometry.property_is_local_at_target.open_cover_tfae AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_TFAE

theorem PropertyIsLocalAtTarget.openCover_iff {P : MorphismProperty Scheme}
    (hP : PropertyIsLocalAtTarget P) {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) :
    P f ↔ ∀ i, P (pullback.snd : pullback f (𝒰.map i) ⟶ _) := by
  -- Porting note : couldn't get the term mode proof work
  refine ⟨fun H => let h := ((hP.openCover_TFAE f).out 0 2).mp H; fun i => ?_,
    fun H => let h := ((hP.openCover_TFAE f).out 1 0).mp; ?_⟩
  · exact h 𝒰 i
    -- 🎉 no goals
  · exact h ⟨𝒰, H⟩
    -- 🎉 no goals
#align algebraic_geometry.property_is_local_at_target.open_cover_iff AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_iff

namespace AffineTargetMorphismProperty

/-- A `P : AffineTargetMorphismProperty` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
def StableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
    P g → P (pullback.fst : pullback f g ⟶ X)
#align algebraic_geometry.affine_target_morphism_property.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.StableUnderBaseChange

theorem IsLocal.targetAffineLocallyPullbackFstOfRightOfStableUnderBaseChange
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) (hP' : P.StableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : P g) :
    targetAffineLocally P (pullback.fst : pullback f g ⟶ X) := by
  -- Porting note : rewrite `(hP.affine_openCover_TFAE ...).out 0 1` doesn't work
  have h01 := (hP.affine_openCover_TFAE (pullback.fst : pullback f g ⟶ X)).out 0 1
  -- ⊢ targetAffineLocally P pullback.fst
  rw [h01]
  -- ⊢ ∃ 𝒰 x, ∀ (i : 𝒰.J), P pullback.snd
  use X.affineCover, inferInstance
  -- ⊢ ∀ (i : (Scheme.affineCover X).J), P pullback.snd
  intro i
  -- ⊢ P pullback.snd
  let e := pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g (X.affineCover.map i)
  -- ⊢ P pullback.snd
  have : e.hom ≫ pullback.fst = pullback.snd := by simp
  -- ⊢ P pullback.snd
  rw [← this, affine_cancel_left_isIso hP.1]
  -- ⊢ P pullback.fst
  apply hP'; assumption
  -- ⊢ P g
             -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_pullback_fst_of_right_of_stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocallyPullbackFstOfRightOfStableUnderBaseChange

theorem IsLocal.stableUnderBaseChange {P : AffineTargetMorphismProperty} (hP : P.IsLocal)
    (hP' : P.StableUnderBaseChange) : (targetAffineLocally P).StableUnderBaseChange :=
  MorphismProperty.StableUnderBaseChange.mk (targetAffineLocally_respectsIso hP.RespectsIso)
    (fun X Y S f g H => by
      -- Porting note : rewrite `(...openCover_TFAE).out 0 1` directly doesn't work, complains about
      -- metavariable
      have h01 := (hP.targetAffineLocallyIsLocal.openCover_TFAE
        (pullback.fst : pullback f g ⟶ X)).out 0 1
      rw [h01]
      -- ⊢ ∃ 𝒰, ∀ (i : 𝒰.J), targetAffineLocally P pullback.snd
      use S.affineCover.pullbackCover f
      -- ⊢ ∀ (i : (Scheme.OpenCover.pullbackCover (Scheme.affineCover S) f).J), targetA …
      intro i
      -- ⊢ targetAffineLocally P pullback.snd
      -- Porting note : rewrite `(hP.affine_openCover_TFAE g).out 0 3` directly doesn't work
      -- complains about metavariable
      have h03 := (hP.affine_openCover_TFAE g).out 0 3
      -- ⊢ targetAffineLocally P pullback.snd
      rw [h03] at H
      -- ⊢ targetAffineLocally P pullback.snd
      let e : pullback (pullback.fst : pullback f g ⟶ _) ((S.affineCover.pullbackCover f).map i) ≅
          _ := by
        refine' pullbackSymmetry _ _ ≪≫ pullbackRightPullbackFstIso f g _ ≪≫ _ ≪≫
          (pullbackRightPullbackFstIso (S.affineCover.map i) g
            (pullback.snd : pullback f (S.affineCover.map i) ⟶ _)).symm
        exact asIso
          (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst = pullback.snd := by simp
      -- ⊢ targetAffineLocally P pullback.snd
      rw [← this, (targetAffineLocally_respectsIso hP.1).cancel_left_isIso]
      -- ⊢ targetAffineLocally P pullback.fst
      apply hP.targetAffineLocallyPullbackFstOfRightOfStableUnderBaseChange hP'
      -- ⊢ P pullback.fst
      rw [← pullbackSymmetry_hom_comp_snd, affine_cancel_left_isIso hP.1]
      -- ⊢ P pullback.snd
      apply H)
      -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.stableUnderBaseChange

end AffineTargetMorphismProperty

/-- The `AffineTargetMorphismProperty` associated to `(targetAffineLocally P).diagonal`.
See `diagonal_targetAffineLocally_eq_targetAffineLocally`.
-/
def AffineTargetMorphismProperty.diagonal (P : AffineTargetMorphismProperty) :
    AffineTargetMorphismProperty :=
  fun {X _} f _ =>
    ∀ {U₁ U₂ : Scheme} (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersion f₁]
      [IsOpenImmersion f₂], P (pullback.mapDesc f₁ f₂ f)
#align algebraic_geometry.affine_target_morphism_property.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.diagonal

theorem AffineTargetMorphismProperty.diagonal_respectsIso (P : AffineTargetMorphismProperty)
    (hP : P.toProperty.RespectsIso) : P.diagonal.toProperty.RespectsIso := by
  delta AffineTargetMorphismProperty.diagonal
  -- ⊢ MorphismProperty.RespectsIso (toProperty fun {X x} f x_1 => ∀ {U₁ U₂ : Schem …
  apply AffineTargetMorphismProperty.respectsIso_mk
  -- ⊢ ∀ {X Y Z : Scheme} (e : X ≅ Y) (f : Y ⟶ Z) [inst : IsAffine Z], (∀ {U₁ U₂ :  …
  · introv H _ _
    -- ⊢ P (pullback.mapDesc f₁ f₂ (e.hom ≫ f))
    rw [pullback.mapDesc_comp, affine_cancel_left_isIso hP, affine_cancel_right_isIso hP]
    -- ⊢ P (pullback.mapDesc (f₁ ≫ e.hom) (f₂ ≫ e.hom) f)
    -- Porting note : add the following two instances
    have i1 : IsOpenImmersion (f₁ ≫ e.hom) := PresheafedSpace.IsOpenImmersion.comp _ _
    -- ⊢ P (pullback.mapDesc (f₁ ≫ e.hom) (f₂ ≫ e.hom) f)
    have i2 : IsOpenImmersion (f₂ ≫ e.hom) := PresheafedSpace.IsOpenImmersion.comp _ _
    -- ⊢ P (pullback.mapDesc (f₁ ≫ e.hom) (f₂ ≫ e.hom) f)
    apply H
    -- 🎉 no goals
  · introv H _ _
    -- ⊢ P (pullback.mapDesc f₁ f₂ (f ≫ e.hom))
    -- Porting note : add the following two instances
    have _ : IsAffine Z := isAffineOfIso e.inv
    -- ⊢ P (pullback.mapDesc f₁ f₂ (f ≫ e.hom))
    rw [pullback.mapDesc_comp, affine_cancel_right_isIso hP]
    -- ⊢ P (pullback.mapDesc f₁ f₂ f)
    apply H
    -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.diagonal_respects_iso AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso

theorem diagonalTargetAffineLocallyOfOpenCover (P : AffineTargetMorphismProperty) (hP : P.IsLocal)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) [∀ i j, IsAffine ((𝒰' i).obj j)]
    (h𝒰' : ∀ i j k, P (pullback.mapDesc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)) :
    (targetAffineLocally P).diagonal f := by
  let 𝒱 := (Scheme.Pullback.openCoverOfBase 𝒰 f f).bind fun i =>
    Scheme.Pullback.openCoverOfLeftRight.{u} (𝒰' i) (𝒰' i) pullback.snd pullback.snd
  have i1 : ∀ i, IsAffine (𝒱.obj i) := fun i => by dsimp; infer_instance
  -- ⊢ MorphismProperty.diagonal (targetAffineLocally P) f
  refine' (hP.affine_openCover_iff _ _).mpr _
  -- ⊢ ∀ (i : 𝒱.J), P pullback.snd
  rintro ⟨i, j, k⟩
  -- ⊢ P pullback.snd
  dsimp
  -- ⊢ P pullback.snd
  convert (affine_cancel_left_isIso hP.1
    (pullbackDiagonalMapIso _ _ ((𝒰' i).map j) ((𝒰' i).map k)).inv pullback.snd).mp _
  pick_goal 3
  · convert h𝒰' i j k; apply pullback.hom_ext <;> simp
    -- ⊢ (pullbackDiagonalMapIso f (Scheme.OpenCover.map 𝒰 i) (Scheme.OpenCover.map ( …
                       -- ⊢ ((pullbackDiagonalMapIso f (Scheme.OpenCover.map 𝒰 i) (Scheme.OpenCover.map  …
                                                  -- 🎉 no goals
                                                  -- 🎉 no goals
  all_goals apply pullback.hom_ext <;>
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
    pullback.lift_snd_assoc]
#align algebraic_geometry.diagonal_target_affine_locally_of_open_cover AlgebraicGeometry.diagonalTargetAffineLocallyOfOpenCover

theorem AffineTargetMorphismProperty.diagonalOfTargetAffineLocally
    (P : AffineTargetMorphismProperty) (hP : P.IsLocal) {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
    [IsAffine U] [IsOpenImmersion g] (H : (targetAffineLocally P).diagonal f) :
    P.diagonal (pullback.snd : pullback f g ⟶ _) := by
  rintro U V f₁ f₂ hU hV hf₁ hf₂
  -- ⊢ P (pullback.mapDesc f₁ f₂ pullback.snd)
  replace H := ((hP.affine_openCover_TFAE (pullback.diagonal f)).out 0 3).mp H
  -- ⊢ P (pullback.mapDesc f₁ f₂ pullback.snd)
  let g₁ := pullback.map (f₁ ≫ pullback.snd) (f₂ ≫ pullback.snd) f f
    (f₁ ≫ pullback.fst) (f₂ ≫ pullback.fst) g
    (by rw [Category.assoc, Category.assoc, pullback.condition])
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  -- Porting note : added this instance
  haveI hg₁ : IsOpenImmersion g₁ := by
    apply (config := { allowSynthFailures := true }) Scheme.pullback_map_isOpenImmersion
    · exact PresheafedSpace.IsOpenImmersion.comp (hf := hf₁) _
    · exact PresheafedSpace.IsOpenImmersion.comp (hf := hf₂) _
  specialize H g₁
  -- ⊢ P (pullback.mapDesc f₁ f₂ pullback.snd)
  rw [← affine_cancel_left_isIso hP.1 (pullbackDiagonalMapIso f _ f₁ f₂).hom]
  -- ⊢ P ((pullbackDiagonalMapIso f g f₁ f₂).hom ≫ pullback.mapDesc f₁ f₂ pullback. …
  convert H
  -- ⊢ (pullbackDiagonalMapIso f g f₁ f₂).hom ≫ pullback.mapDesc f₁ f₂ pullback.snd …
  · apply pullback.hom_ext <;>
    -- ⊢ ((pullbackDiagonalMapIso f g f₁ f₂).hom ≫ pullback.mapDesc f₁ f₂ pullback.sn …
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.comp_id, pullbackDiagonalMapIso_hom_fst,
      pullbackDiagonalMapIso_hom_snd]
#align algebraic_geometry.affine_target_morphism_property.diagonal_of_target_affine_locally AlgebraicGeometry.AffineTargetMorphismProperty.diagonalOfTargetAffineLocally

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
  -- ⊢ MorphismProperty.diagonal (targetAffineLocally P) f → ∀ {U : Scheme} (g : U  …
  · introv H hU hg _ _; apply P.diagonalOfTargetAffineLocally <;> assumption
    -- ⊢ P (pullback.mapDesc f₁ f₂ pullback.snd)
                        -- ⊢ IsLocal P
                                                                  -- 🎉 no goals
                                                                  -- 🎉 no goals
  tfae_have 4 → 3
  -- ⊢ (∀ {U : Scheme} (g : U ⟶ Y) [inst : IsAffine U] [inst_1 : IsOpenImmersion g] …
  · introv H h𝒰; apply H
    -- ⊢ ∀ [inst : IsOpenImmersion f₁] [inst : IsOpenImmersion f₂], P (pullback.mapDe …
                 -- 🎉 no goals
  tfae_have 3 → 2
  -- ⊢ (∀ (𝒰 : Scheme.OpenCover Y) [inst : ∀ (i : 𝒰.J), IsAffine (Scheme.OpenCover. …
  · exact fun H => ⟨Y.affineCover, inferInstance, H Y.affineCover⟩
    -- 🎉 no goals
  tfae_have 2 → 5
  -- ⊢ (∃ 𝒰 x, ∀ (i : 𝒰.J), diagonal P pullback.snd) → ∃ 𝒰 x 𝒰' x_1, ∀ (i : 𝒰.J) (j …
  · rintro ⟨𝒰, h𝒰, H⟩
    -- ⊢ ∃ 𝒰 x 𝒰' x_1, ∀ (i : 𝒰.J) (j k : (𝒰' i).J), P (pullback.mapDesc (Scheme.Open …
    refine' ⟨𝒰, inferInstance, fun _ => Scheme.affineCover _, inferInstance, _⟩
    -- ⊢ ∀ (i : 𝒰.J) (j k : ((fun x => Scheme.affineCover (pullback f (Scheme.OpenCov …
    intro i j k
    -- ⊢ P (pullback.mapDesc (Scheme.OpenCover.map ((fun x => Scheme.affineCover (pul …
    apply H
    -- 🎉 no goals
  tfae_have 5 → 1
  -- ⊢ (∃ 𝒰 x 𝒰' x_1, ∀ (i : 𝒰.J) (j k : (𝒰' i).J), P (pullback.mapDesc (Scheme.Ope …
  · rintro ⟨𝒰, _, 𝒰', _, H⟩
    -- ⊢ MorphismProperty.diagonal (targetAffineLocally P) f
    exact diagonalTargetAffineLocallyOfOpenCover P hP f 𝒰 𝒰' H
    -- 🎉 no goals
  tfae_finish
  -- 🎉 no goals
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal_affine_open_cover_tfae AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.diagonal_affine_openCover_TFAE

theorem AffineTargetMorphismProperty.IsLocal.diagonal {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) : P.diagonal.IsLocal :=
  AffineTargetMorphismProperty.isLocalOfOpenCoverImply P.diagonal (P.diagonal_respectsIso hP.1)
    fun {_ _} f => ((hP.diagonal_affine_openCover_TFAE f).out 1 3).mp
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.diagonal

theorem diagonal_targetAffineLocally_eq_targetAffineLocally (P : AffineTargetMorphismProperty)
    (hP : P.IsLocal) : (targetAffineLocally P).diagonal = targetAffineLocally P.diagonal := by
  -- Porting note : `ext _ _ f` fails at first one
  -- see https://github.com/leanprover-community/mathlib4/issues/5229
  refine funext fun _ => funext fun _ => funext fun f => propext ?_
  -- ⊢ MorphismProperty.diagonal (targetAffineLocally P) f ↔ targetAffineLocally (A …
  exact ((hP.diagonal_affine_openCover_TFAE f).out 0 1).trans
    ((hP.diagonal.affine_openCover_TFAE f).out 1 0)
#align algebraic_geometry.diagonal_target_affine_locally_eq_target_affine_locally AlgebraicGeometry.diagonal_targetAffineLocally_eq_targetAffineLocally

theorem universallyIsLocalAtTarget (P : MorphismProperty Scheme)
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
      (∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) → P f) :
    PropertyIsLocalAtTarget P.universally := by
  refine' ⟨P.universally_respectsIso, fun {X Y} f U =>
    P.universally_stableUnderBaseChange (isPullback_morphismRestrict f U).flip, _⟩
  intro X Y f 𝒰 h X' Y' i₁ i₂ f' H
  -- ⊢ P f'
  apply hP _ (𝒰.pullbackCover i₂)
  -- ⊢ ∀ (i : (Scheme.OpenCover.pullbackCover 𝒰 i₂).J), P pullback.snd
  intro i
  -- ⊢ P pullback.snd
  dsimp
  -- ⊢ P pullback.snd
  apply h i (pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ pullback.snd) _) pullback.snd
  -- ⊢ IsPullback pullback.snd (pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ p …
  swap
  -- ⊢ (pullback.fst ≫ i₁) ≫ f = (pullback.snd ≫ pullback.snd) ≫ Scheme.OpenCover.m …
  · rw [Category.assoc, Category.assoc, ← pullback.condition, ← pullback.condition_assoc, H.w]
    -- 🎉 no goals
  refine' (IsPullback.of_right _ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)).flip
  -- ⊢ IsPullback (pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ pullback.snd)  …
  rw [pullback.lift_fst, ← pullback.condition]
  -- ⊢ IsPullback (pullback.fst ≫ i₁) pullback.snd f (pullback.fst ≫ i₂)
  exact (IsPullback.of_hasPullback _ _).paste_horiz H.flip
  -- 🎉 no goals
#align algebraic_geometry.universally_is_local_at_target AlgebraicGeometry.universallyIsLocalAtTarget

theorem universallyIsLocalAtTargetOfMorphismRestrict (P : MorphismProperty Scheme)
    (hP₁ : P.RespectsIso)
    (hP₂ : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y.carrier)
      (_ : iSup U = ⊤), (∀ i, P (f ∣_ U i)) → P f) : PropertyIsLocalAtTarget P.universally :=
  universallyIsLocalAtTarget P (fun f 𝒰 h𝒰 => by
    apply hP₂ f (fun i : 𝒰.J => Scheme.Hom.opensRange (𝒰.map i)) 𝒰.iSup_opensRange
    -- ⊢ ∀ (i : 𝒰.J), P (f ∣_ Scheme.Hom.opensRange (Scheme.OpenCover.map 𝒰 i))
    simp_rw [hP₁.arrow_mk_iso_iff (morphismRestrictOpensRange f _)]
    -- ⊢ ∀ (i : 𝒰.J), P pullback.snd
    exact h𝒰)
    -- 🎉 no goals
#align algebraic_geometry.universally_is_local_at_target_of_morphism_restrict AlgebraicGeometry.universallyIsLocalAtTargetOfMorphismRestrict

/-- `topologically P` holds for a morphism if the underlying topological map satisfies `P`. -/
def MorphismProperty.topologically
    (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (_ : α → β), Prop) :
    MorphismProperty Scheme.{u} := fun _ _ f => P f.1.base
#align algebraic_geometry.morphism_property.topologically AlgebraicGeometry.MorphismProperty.topologically

end AlgebraicGeometry

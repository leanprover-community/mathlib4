/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang

! This file was ported from Lean 3 source module algebraic_geometry.morphisms.basic
! leanprover-community/mathlib commit 434e2fd21c1900747afc6d13d8be7f4eedba7218
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.CategoryTheory.MorphismProperty

/-!
# Properties of morphisms between Schemes

We provide the basic framework for talking about properties of morphisms between Schemes.

A `morphism_property Scheme` is a predicate on morphisms between schemes, and an
`affine_target_morphism_property` is a predicate on morphisms into affine schemes. Given a
`P : affine_target_morphism_property`, we may construct a `morphism_property` called
`target_affine_locally P` that holds for `f : X ⟶ Y` whenever `P` holds for the
restriction of `f` on every affine open subset of `Y`.

## Main definitions

- `algebraic_geometry.affine_target_morphism_property.is_local`: We say that `P.is_local` if `P`
satisfies the assumptions of the affine communication lemma
(`algebraic_geometry.of_affine_open_cover`). That is,
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basic_open r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basic_open r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.

- `algebraic_geometry.property_is_local_at_target`: We say that `property_is_local_at_target P` for
`P : morphism_property Scheme` if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.

## Main results

- `algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_tfae`:
  If `P.is_local`, then `target_affine_locally P f` iff there exists an affine cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.
- `algebraic_geometry.affine_target_morphism_property.is_local_of_open_cover_imply`:
  If the existance of an affine cover `{ Uᵢ }` of `Y` such that `P` holds for `f ∣_ Uᵢ` implies
  `target_affine_locally P f`, then `P.is_local`.
- `algebraic_geometry.affine_target_morphism_property.is_local.affine_target_iff`:
  If `Y` is affine and `f : X ⟶ Y`, then `target_affine_locally P f ↔ P f` provided `P.is_local`.
- `algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local` :
  If `P.is_local`, then `property_is_local_at_target (target_affine_locally P)`.
- `algebraic_geometry.property_is_local_at_target.open_cover_tfae`:
  If `property_is_local_at_target P`, then `P f` iff there exists an open cover `{ Uᵢ }` of `Y`
  such that `P` holds for `f ∣_ Uᵢ`.

These results should not be used directly, and should be ported to each property that is local.

-/


universe u

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace AlgebraicGeometry

/-- An `affine_target_morphism_property` is a class of morphisms from an arbitrary scheme into an
affine scheme. -/
def AffineTargetMorphismProperty :=
  ∀ ⦃X Y : Scheme⦄ (f : X ⟶ Y) [IsAffine Y], Prop
#align algebraic_geometry.affine_target_morphism_property AlgebraicGeometry.AffineTargetMorphismProperty

/-- `is_iso` as a `morphism_property`. -/
protected def Scheme.isIso : MorphismProperty Scheme :=
  @IsIso Scheme _
#align algebraic_geometry.Scheme.is_iso AlgebraicGeometry.Scheme.isIso

/-- `is_iso` as an `affine_morphism_property`. -/
protected def Scheme.affineTargetIsIso : AffineTargetMorphismProperty := fun X Y f H => IsIso f
#align algebraic_geometry.Scheme.affine_target_is_iso AlgebraicGeometry.Scheme.affineTargetIsIso

instance : Inhabited AffineTargetMorphismProperty :=
  ⟨Scheme.affineTargetIsIso⟩

/-- A `affine_target_morphism_property` can be extended to a `morphism_property` such that it
*never* holds when the target is not affine -/
def AffineTargetMorphismProperty.toProperty (P : AffineTargetMorphismProperty) :
    MorphismProperty Scheme := fun X Y f => ∃ h, @P f h
#align algebraic_geometry.affine_target_morphism_property.to_property AlgebraicGeometry.AffineTargetMorphismProperty.toProperty

theorem AffineTargetMorphismProperty.toProperty_apply (P : AffineTargetMorphismProperty)
    {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y] : P.toProperty f ↔ P f := by
  delta affine_target_morphism_property.to_property; simp [*]
#align algebraic_geometry.affine_target_morphism_property.to_property_apply AlgebraicGeometry.AffineTargetMorphismProperty.toProperty_apply

theorem affine_cancel_left_isIso {P : AffineTargetMorphismProperty} (hP : P.toProperty.RespectsIso)
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso f] [IsAffine Z] : P (f ≫ g) ↔ P g := by
  rw [← P.to_property_apply, ← P.to_property_apply, hP.cancel_left_is_iso]
#align algebraic_geometry.affine_cancel_left_is_iso AlgebraicGeometry.affine_cancel_left_isIso

theorem affine_cancel_right_isIso {P : AffineTargetMorphismProperty} (hP : P.toProperty.RespectsIso)
    {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [IsIso g] [IsAffine Z] [IsAffine Y] :
    P (f ≫ g) ↔ P f := by rw [← P.to_property_apply, ← P.to_property_apply, hP.cancel_right_is_iso]
#align algebraic_geometry.affine_cancel_right_is_iso AlgebraicGeometry.affine_cancel_right_isIso

theorem AffineTargetMorphismProperty.respectsIso_mk {P : AffineTargetMorphismProperty}
    (h₁ : ∀ {X Y Z} (e : X ≅ Y) (f : Y ⟶ Z) [IsAffine Z], P f → P (e.hom ≫ f))
    (h₂ :
      ∀ {X Y Z} (e : Y ≅ Z) (f : X ⟶ Y) [h : IsAffine Y],
        P f → @P (f ≫ e.hom) (is_affine_of_iso e.inv)) :
    P.toProperty.RespectsIso := by
  constructor
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨a, h₁ e f h⟩
  · rintro X Y Z e f ⟨a, h⟩; exact ⟨is_affine_of_iso e.inv, h₂ e f h⟩
#align algebraic_geometry.affine_target_morphism_property.respects_iso_mk AlgebraicGeometry.AffineTargetMorphismProperty.respectsIso_mk

/-- For a `P : affine_target_morphism_property`, `target_affine_locally P` holds for
`f : X ⟶ Y` whenever `P` holds for the restriction of `f` on every affine open subset of `Y`. -/
def targetAffineLocally (P : AffineTargetMorphismProperty) : MorphismProperty Scheme :=
  fun {X Y : Scheme} (f : X ⟶ Y) => ∀ U : Y.affineOpens, @P (f ∣_ U) U.Prop
#align algebraic_geometry.target_affine_locally AlgebraicGeometry.targetAffineLocally

theorem IsAffineOpen.map_isIso {X Y : Scheme} {U : Opens Y.carrier} (hU : IsAffineOpen U)
    (f : X ⟶ Y) [IsIso f] : IsAffineOpen ((Opens.map f.1.base).obj U) :=
  haveI : is_affine _ := hU
  is_affine_of_iso (f ∣_ U)
#align algebraic_geometry.is_affine_open.map_is_iso AlgebraicGeometry.IsAffineOpen.map_isIso

theorem targetAffineLocally_respectsIso {P : AffineTargetMorphismProperty}
    (hP : P.toProperty.RespectsIso) : (targetAffineLocally P).RespectsIso := by
  constructor
  · introv H U
    rw [morphism_restrict_comp, affine_cancel_left_is_iso hP]
    exact H U
  · introv H
    rintro ⟨U, hU : is_affine_open U⟩; dsimp
    haveI : is_affine _ := hU
    haveI : is_affine _ := hU.map_is_iso e.hom
    rw [morphism_restrict_comp, affine_cancel_right_is_iso hP]
    exact H ⟨(opens.map e.hom.val.base).obj U, hU.map_is_iso e.hom⟩
#align algebraic_geometry.target_affine_locally_respects_iso AlgebraicGeometry.targetAffineLocally_respectsIso

/-- We say that `P : affine_target_morphism_property` is a local property if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ Y.basic_open r` for any
  global section `r`.
3. If `P` holds for `f ∣_ Y.basic_open r` for all `r` in a spanning set of the global sections,
  then `P` holds for `f`.
-/
structure AffineTargetMorphismProperty.IsLocal (P : AffineTargetMorphismProperty) : Prop where
  RespectsIso : P.toProperty.RespectsIso
  toBasicOpen :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (r : Y.Presheaf.obj <| op ⊤),
      P f → @P (f ∣_ Y.basic_open r) ((top_is_affine_open Y).basicOpenIsAffine _)
  ofBasicOpenCover :
    ∀ {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y) (s : Finset (Y.Presheaf.obj <| op ⊤))
      (hs : Ideal.span (s : Set (Y.Presheaf.obj <| op ⊤)) = ⊤),
      (∀ r : s, @P (f ∣_ Y.basic_open r.1) ((top_is_affine_open Y).basicOpenIsAffine _)) → P f
#align algebraic_geometry.affine_target_morphism_property.is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal

theorem targetAffineLocallyOfOpenCover {P : AffineTargetMorphismProperty} (hP : P.IsLocal)
    {X Y : Scheme} (f : X ⟶ Y) (𝒰 : Y.OpenCover) [∀ i, IsAffine (𝒰.obj i)]
    (h𝒰 : ∀ i, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) : targetAffineLocally P f :=
  by
  classical
  let S i :=
    (⟨⟨Set.range (𝒰.map i).1.base, (𝒰.is_open i).base_open.open_range⟩,
        range_is_affine_open_of_open_immersion (𝒰.map i)⟩ :
      Y.affine_opens)
  intro U
  apply of_affine_open_cover U (Set.range S)
  · intro U r h
    haveI : is_affine _ := U.2
    have := hP.2 (f ∣_ U.1)
    replace this := this (Y.presheaf.map (eq_to_hom U.1.openEmbedding_obj_top).op r) h
    rw [← P.to_property_apply] at this ⊢
    exact (hP.1.arrow_mk_iso_iff (morphism_restrict_restrict_basic_open f _ r)).mp this
  · intro U s hs H
    haveI : is_affine _ := U.2
    apply hP.3 (f ∣_ U.1) (s.image (Y.presheaf.map (eq_to_hom U.1.openEmbedding_obj_top).op))
    · apply_fun Ideal.comap (Y.presheaf.map (eq_to_hom U.1.openEmbedding_obj_top.symm).op) at hs 
      rw [Ideal.comap_top] at hs 
      rw [← hs]
      simp only [eq_to_hom_op, eq_to_hom_map, Finset.coe_image]
      have :
        ∀ {R S : CommRingCat} (e : S = R) (s : Set S),
          Ideal.span (eq_to_hom e '' s) = Ideal.comap (eq_to_hom e.symm) (Ideal.span s) :=
        by intros; subst e; simpa
      apply this
    · rintro ⟨r, hr⟩
      obtain ⟨r, hr', rfl⟩ := finset.mem_image.mp hr
      simp_rw [← P.to_property_apply] at H ⊢
      exact (hP.1.arrow_mk_iso_iff (morphism_restrict_restrict_basic_open f _ r)).mpr (H ⟨r, hr'⟩)
  · rw [Set.eq_univ_iff_forall]
    simp only [Set.mem_iUnion]
    intro x
    exact ⟨⟨_, ⟨𝒰.f x, rfl⟩⟩, 𝒰.covers x⟩
  · rintro ⟨_, i, rfl⟩
    simp_rw [← P.to_property_apply] at h𝒰 ⊢
    exact (hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)).mpr (h𝒰 i)
#align algebraic_geometry.target_affine_locally_of_open_cover AlgebraicGeometry.targetAffineLocallyOfOpenCover

theorem AffineTargetMorphismProperty.IsLocal.affine_openCover_tFAE
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [targetAffineLocally P f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersionCat g],
          P (pullback.snd : pullback f g ⟶ U),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (hU : iSup U = ⊤) (hU' : ∀ i, IsAffineOpen (U i)),
          ∀ i, @P (f ∣_ U i) (hU' i)] := by
  tfae_have 1 → 4
  · intro H U g h₁ h₂
    skip
    replace H := H ⟨⟨_, h₂.base_open.open_range⟩, range_is_affine_open_of_open_immersion g⟩
    rw [← P.to_property_apply] at H ⊢
    rwa [← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)]
  tfae_have 4 → 3
  · intro H 𝒰 h𝒰 i
    skip
    apply H
  tfae_have 3 → 2
  · exact fun H => ⟨Y.affine_cover, inferInstance, H Y.affine_cover⟩
  tfae_have 2 → 1
  · rintro ⟨𝒰, h𝒰, H⟩; exact target_affine_locally_of_open_cover hP f 𝒰 H
  tfae_have 5 → 2
  · rintro ⟨ι, U, hU, hU', H⟩
    refine' ⟨Y.open_cover_of_supr_eq_top U hU, hU', _⟩
    intro i
    specialize H i
    rw [← P.to_property_apply, ← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)]
    rw [← P.to_property_apply] at H 
    convert H
    all_goals ext1; exact Subtype.range_coe
  tfae_have 1 → 5
  · intro H
    refine'
      ⟨Y.carrier, fun x => (Y.affine_cover.map x).opensRange, _, fun i =>
        range_is_affine_open_of_open_immersion _, _⟩
    · rw [eq_top_iff]; intro x _; erw [opens.mem_supr]; exact ⟨x, Y.affine_cover.covers x⟩
    · intro i; exact H ⟨_, range_is_affine_open_of_open_immersion _⟩
  tfae_finish
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_tfae AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_tFAE

theorem AffineTargetMorphismProperty.isLocalOfOpenCoverImply (P : AffineTargetMorphismProperty)
    (hP : P.toProperty.RespectsIso)
    (H :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        (∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
            ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullback_cover f).obj i ⟶ 𝒰.obj i)) →
          ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersionCat g],
            P (pullback.snd : pullback f g ⟶ U)) :
    P.IsLocal := by
  refine' ⟨hP, _, _⟩
  · introv h
    skip
    haveI : is_affine _ := (top_is_affine_open Y).basicOpenIsAffine r
    delta morphism_restrict
    rw [affine_cancel_left_is_iso hP]
    refine' @H f ⟨Scheme.open_cover_of_is_iso (𝟙 Y), _, _⟩ (Y.of_restrict _) _inst _
    · intro i; dsimp; infer_instance
    · intro i; dsimp
      rwa [← category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_is_iso hP]
  · introv hs hs'
    skip
    replace hs := ((top_is_affine_open Y).basicOpen_union_eq_self_iff _).mpr hs
    have := H f ⟨Y.open_cover_of_supr_eq_top _ hs, _, _⟩ (𝟙 _)
    rwa [← category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_is_iso hP] at
      this 
    · intro i; exact (top_is_affine_open Y).basicOpenIsAffine _
    · rintro (i : s)
      specialize hs' i
      haveI : is_affine _ := (top_is_affine_open Y).basicOpenIsAffine i.1
      delta morphism_restrict at hs' 
      rwa [affine_cancel_left_is_iso hP] at hs' 
#align algebraic_geometry.affine_target_morphism_property.is_local_of_open_cover_imply AlgebraicGeometry.AffineTargetMorphismProperty.isLocalOfOpenCoverImply

theorem AffineTargetMorphismProperty.IsLocal.affine_openCover_iff {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y)
    [h𝒰 : ∀ i, IsAffine (𝒰.obj i)] :
    targetAffineLocally P f ↔ ∀ i, @P (pullback.snd : pullback f (𝒰.map i) ⟶ _) (h𝒰 i) :=
  ⟨fun H =>
    let h := ((hP.affine_openCover_tFAE f).out 0 2).mp H
    h 𝒰,
    fun H =>
    let h := ((hP.affine_openCover_tFAE f).out 1 0).mp
    h ⟨𝒰, inferInstance, H⟩⟩
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_open_cover_iff AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_openCover_iff

theorem AffineTargetMorphismProperty.IsLocal.affine_target_iff {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine Y] : targetAffineLocally P f ↔ P f :=
  by
  rw [hP.affine_open_cover_iff f _]
  swap; · exact Scheme.open_cover_of_is_iso (𝟙 Y)
  swap; · intro; dsimp; infer_instance
  trans P (pullback.snd : pullback f (𝟙 _) ⟶ _)
  · exact ⟨fun H => H PUnit.unit, fun H _ => H⟩
  rw [← category.comp_id pullback.snd, ← pullback.condition, affine_cancel_left_is_iso hP.1]
#align algebraic_geometry.affine_target_morphism_property.is_local.affine_target_iff AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.affine_target_iff

/-- We say that `P : morphism_property Scheme` is local at the target if
1. `P` respects isomorphisms.
2. If `P` holds for `f : X ⟶ Y`, then `P` holds for `f ∣_ U` for any `U`.
3. If `P` holds for `f ∣_ U` for an open cover `U` of `Y`, then `P` holds for `f`.
-/
structure PropertyIsLocalAtTarget (P : MorphismProperty Scheme) : Prop where
  RespectsIso : P.RespectsIso
  restrict : ∀ {X Y : Scheme} (f : X ⟶ Y) (U : Opens Y.carrier), P f → P (f ∣_ U)
  of_open_cover :
    ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
      (∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) → P f
#align algebraic_geometry.property_is_local_at_target AlgebraicGeometry.PropertyIsLocalAtTarget

theorem AffineTargetMorphismProperty.IsLocal.targetAffineLocallyIsLocal
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) :
    PropertyIsLocalAtTarget (targetAffineLocally P) := by
  constructor
  · exact target_affine_locally_respects_iso hP.1
  · intro X Y f U H V
    rw [← P.to_property_apply, hP.1.arrow_mk_iso_iff (morphism_restrict_restrict f _ _)]
    convert H ⟨_, is_affine_open.image_is_open_immersion V.2 (Y.of_restrict _)⟩
    rw [← P.to_property_apply]
    rfl
  · rintro X Y f 𝒰 h𝒰
    rw [(hP.affine_open_cover_tfae f).out 0 1]
    refine' ⟨𝒰.bind fun _ => Scheme.affine_cover _, _, _⟩
    · intro i; dsimp [Scheme.open_cover.bind]; infer_instance
    · intro i
      specialize h𝒰 i.1
      rw [(hP.affine_open_cover_tfae (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)).out 0 2] at h𝒰 
      specialize h𝒰 (Scheme.affine_cover _) i.2
      let e :
        pullback f ((𝒰.obj i.fst).affineCover.map i.snd ≫ 𝒰.map i.fst) ⟶
          pullback (pullback.snd : pullback f (𝒰.map i.fst) ⟶ _)
            ((𝒰.obj i.fst).affineCover.map i.snd) := by
        refine' (pullback_symmetry _ _).Hom ≫ _
        refine' (pullback_right_pullback_fst_iso _ _ _).inv ≫ _
        refine' (pullback_symmetry _ _).Hom ≫ _
        refine' pullback.map _ _ _ _ (pullback_symmetry _ _).Hom (𝟙 _) (𝟙 _) _ _ <;>
          simp only [category.comp_id, category.id_comp, pullback_symmetry_hom_comp_snd]
      rw [← affine_cancel_left_is_iso hP.1 e] at h𝒰 
      convert h𝒰
      simp
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_is_local AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocallyIsLocal

theorem PropertyIsLocalAtTarget.openCover_tFAE {P : MorphismProperty Scheme}
    (hP : PropertyIsLocalAtTarget P) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [P f,
        ∃ 𝒰 : Scheme.OpenCover.{u} Y,
          ∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) (i : 𝒰.J),
          P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i),
        ∀ U : Opens Y.carrier, P (f ∣_ U),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsOpenImmersionCat g], P (pullback.snd : pullback f g ⟶ U),
        ∃ (ι : Type u) (U : ι → Opens Y.carrier) (hU : iSup U = ⊤), ∀ i, P (f ∣_ U i)] := by
  tfae_have 2 → 1
  · rintro ⟨𝒰, H⟩; exact hP.3 f 𝒰 H
  tfae_have 1 → 4
  · intro H U; exact hP.2 f U H
  tfae_have 4 → 3
  · intro H 𝒰 i
    rw [← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)]
    exact H (𝒰.map i).opensRange
  tfae_have 3 → 2
  · exact fun H => ⟨Y.affine_cover, H Y.affine_cover⟩
  tfae_have 4 → 5
  · intro H U g hg
    skip
    rw [← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)]
    apply H
  tfae_have 5 → 4
  · intro H U
    erw [hP.1.cancel_left_isIso]
    apply H
  tfae_have 4 → 6
  · intro H; exact ⟨PUnit, fun _ => ⊤, ciSup_const, fun _ => H _⟩
  tfae_have 6 → 2
  · rintro ⟨ι, U, hU, H⟩
    refine' ⟨Y.open_cover_of_supr_eq_top U hU, _⟩
    intro i
    rw [← hP.1.arrow_mk_iso_iff (morphism_restrict_opens_range f _)]
    convert H i
    all_goals ext1; exact Subtype.range_coe
  tfae_finish
#align algebraic_geometry.property_is_local_at_target.open_cover_tfae AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_tFAE

theorem PropertyIsLocalAtTarget.openCover_iff {P : MorphismProperty Scheme}
    (hP : PropertyIsLocalAtTarget P) {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) :
    P f ↔ ∀ i, P (pullback.snd : pullback f (𝒰.map i) ⟶ _) :=
  ⟨fun H =>
    let h := ((hP.openCover_tFAE f).out 0 2).mp H
    h 𝒰,
    fun H =>
    let h := ((hP.openCover_tFAE f).out 1 0).mp
    h ⟨𝒰, H⟩⟩
#align algebraic_geometry.property_is_local_at_target.open_cover_iff AlgebraicGeometry.PropertyIsLocalAtTarget.openCover_iff

namespace AffineTargetMorphismProperty

/-- A `P : affine_target_morphism_property` is stable under base change if `P` holds for `Y ⟶ S`
implies that `P` holds for `X ×ₛ Y ⟶ X` with `X` and `S` affine schemes. -/
def StableUnderBaseChange (P : AffineTargetMorphismProperty) : Prop :=
  ∀ ⦃X Y S : Scheme⦄ [IsAffine S] [IsAffine X] (f : X ⟶ S) (g : Y ⟶ S),
    P g → P (pullback.fst : pullback f g ⟶ X)
#align algebraic_geometry.affine_target_morphism_property.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.StableUnderBaseChange

theorem IsLocal.targetAffineLocallyPullbackFstOfRightOfStableUnderBaseChange
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) (hP' : P.StableUnderBaseChange)
    {X Y S : Scheme} (f : X ⟶ S) (g : Y ⟶ S) [IsAffine S] (H : P g) :
    targetAffineLocally P (pullback.fst : pullback f g ⟶ X) := by
  rw [(hP.affine_open_cover_tfae (pullback.fst : pullback f g ⟶ X)).out 0 1]
  use X.affine_cover, inferInstance
  intro i
  let e := pullback_symmetry _ _ ≪≫ pullback_right_pullback_fst_iso f g (X.affine_cover.map i)
  have : e.hom ≫ pullback.fst = pullback.snd := by simp
  rw [← this, affine_cancel_left_is_iso hP.1]
  apply hP' <;> assumption
#align algebraic_geometry.affine_target_morphism_property.is_local.target_affine_locally_pullback_fst_of_right_of_stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.targetAffineLocallyPullbackFstOfRightOfStableUnderBaseChange

theorem IsLocal.stableUnderBaseChange {P : AffineTargetMorphismProperty} (hP : P.IsLocal)
    (hP' : P.StableUnderBaseChange) : (targetAffineLocally P).StableUnderBaseChange :=
  MorphismProperty.StableUnderBaseChange.mk (targetAffineLocally_respectsIso hP.RespectsIso)
    (by
      intro X Y S f g H
      rw [(hP.target_affine_locally_is_local.open_cover_tfae (pullback.fst : pullback f g ⟶ X)).out
          0 1]
      use S.affine_cover.pullback_cover f
      intro i
      rw [(hP.affine_open_cover_tfae g).out 0 3] at H 
      let e :
        pullback (pullback.fst : pullback f g ⟶ _) ((S.affine_cover.pullback_cover f).map i) ≅ _ :=
        by
        refine'
          pullback_symmetry _ _ ≪≫
            pullback_right_pullback_fst_iso f g _ ≪≫
              _ ≪≫
                (pullback_right_pullback_fst_iso (S.affine_cover.map i) g
                    (pullback.snd : pullback f (S.affine_cover.map i) ⟶ _)).symm
        exact
          as_iso
            (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) (by simpa using pullback.condition) (by simp))
      have : e.hom ≫ pullback.fst = pullback.snd := by simp
      rw [← this, (target_affine_locally_respects_iso hP.1).cancel_left_isIso]
      apply hP.target_affine_locally_pullback_fst_of_right_of_stable_under_base_change hP'
      rw [← pullback_symmetry_hom_comp_snd, affine_cancel_left_is_iso hP.1]
      apply H)
#align algebraic_geometry.affine_target_morphism_property.is_local.stable_under_base_change AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.stableUnderBaseChange

end AffineTargetMorphismProperty

/-- The `affine_target_morphism_property` associated to `(target_affine_locally P).diagonal`.
See `diagonal_target_affine_locally_eq_target_affine_locally`.
-/
def AffineTargetMorphismProperty.diagonal (P : AffineTargetMorphismProperty) :
    AffineTargetMorphismProperty := fun X Y f hf =>
  ∀ {U₁ U₂ : Scheme} (f₁ : U₁ ⟶ X) (f₂ : U₂ ⟶ X) [IsAffine U₁] [IsAffine U₂] [IsOpenImmersionCat f₁]
    [IsOpenImmersionCat f₂], P (pullback.map_desc f₁ f₂ f)
#align algebraic_geometry.affine_target_morphism_property.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.diagonal

theorem AffineTargetMorphismProperty.diagonal_respectsIso (P : AffineTargetMorphismProperty)
    (hP : P.toProperty.RespectsIso) : P.diagonal.toProperty.RespectsIso := by
  delta affine_target_morphism_property.diagonal
  apply affine_target_morphism_property.respects_iso_mk
  · introv H _ _
    skip
    rw [pullback.map_desc_comp, affine_cancel_left_is_iso hP, affine_cancel_right_is_iso hP]
    apply H
  · introv H _ _
    skip
    rw [pullback.map_desc_comp, affine_cancel_right_is_iso hP]
    apply H
#align algebraic_geometry.affine_target_morphism_property.diagonal_respects_iso AlgebraicGeometry.AffineTargetMorphismProperty.diagonal_respectsIso

theorem diagonalTargetAffineLocallyOfOpenCover (P : AffineTargetMorphismProperty) (hP : P.IsLocal)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)]
    (𝒰' : ∀ i, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) [∀ i j, IsAffine ((𝒰' i).obj j)]
    (h𝒰' : ∀ i j k, P (pullback.mapDesc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)) :
    (targetAffineLocally P).diagonal f := by
  refine' (hP.affine_open_cover_iff _ _).mpr _
  ·
    exact
      (Scheme.pullback.open_cover_of_base 𝒰 f f).bind fun i =>
        Scheme.Pullback.openCoverOfLeftRight.{u, u} (𝒰' i) (𝒰' i) pullback.snd pullback.snd
  · intro i
    dsimp at *
    infer_instance
  · rintro ⟨i, j, k⟩
    dsimp
    convert
      (affine_cancel_left_is_iso hP.1
            (pullback_diagonal_map_iso _ _ ((𝒰' i).map j) ((𝒰' i).map k)).inv pullback.snd).mp
        _
    pick_goal 3
    · convert h𝒰' i j k; apply pullback.hom_ext <;> simp
    all_goals
      apply pullback.hom_ext <;>
        simp only [category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
          pullback.lift_snd_assoc]
#align algebraic_geometry.diagonal_target_affine_locally_of_open_cover AlgebraicGeometry.diagonalTargetAffineLocallyOfOpenCover

theorem AffineTargetMorphismProperty.diagonalOfTargetAffineLocally
    (P : AffineTargetMorphismProperty) (hP : P.IsLocal) {X Y U : Scheme.{u}} (f : X ⟶ Y) (g : U ⟶ Y)
    [IsAffine U] [IsOpenImmersionCat g] (H : (targetAffineLocally P).diagonal f) :
    P.diagonal (pullback.snd : pullback f g ⟶ _) := by
  rintro U V f₁ f₂ _ _ _ _
  skip
  replace H := ((hP.affine_open_cover_tfae (pullback.diagonal f)).out 0 3).mp H
  let g₁ :=
    pullback.map (f₁ ≫ pullback.snd) (f₂ ≫ pullback.snd) f f (f₁ ≫ pullback.fst) (f₂ ≫ pullback.fst)
      g (by rw [category.assoc, category.assoc, pullback.condition])
      (by rw [category.assoc, category.assoc, pullback.condition])
  let g₂ : pullback f₁ f₂ ⟶ pullback f g := pullback.fst ≫ f₁
  specialize H g₁
  rw [← affine_cancel_left_is_iso hP.1 (pullback_diagonal_map_iso f _ f₁ f₂).Hom]
  convert H
  ·
    apply pullback.hom_ext <;>
      simp only [category.assoc, pullback.lift_fst, pullback.lift_snd, pullback.lift_fst_assoc,
        pullback.lift_snd_assoc, category.comp_id, pullback_diagonal_map_iso_hom_fst,
        pullback_diagonal_map_iso_hom_snd]
#align algebraic_geometry.affine_target_morphism_property.diagonal_of_target_affine_locally AlgebraicGeometry.AffineTargetMorphismProperty.diagonalOfTargetAffineLocally

theorem AffineTargetMorphismProperty.IsLocal.diagonal_affine_openCover_tFAE
    {P : AffineTargetMorphismProperty} (hP : P.IsLocal) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    TFAE
      [(targetAffineLocally P).diagonal f,
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)),
          ∀ i : 𝒰.J, P.diagonal (pullback.snd : pullback f (𝒰.map i) ⟶ _),
        ∀ (𝒰 : Scheme.OpenCover.{u} Y) [∀ i, IsAffine (𝒰.obj i)] (i : 𝒰.J),
          P.diagonal (pullback.snd : pullback f (𝒰.map i) ⟶ _),
        ∀ {U : Scheme} (g : U ⟶ Y) [IsAffine U] [IsOpenImmersionCat g],
          P.diagonal (pullback.snd : pullback f g ⟶ _),
        ∃ (𝒰 : Scheme.OpenCover.{u} Y) (_ : ∀ i, IsAffine (𝒰.obj i)) (𝒰' :
          ∀ i, Scheme.OpenCover.{u} (pullback f (𝒰.map i))) (_ : ∀ i j, IsAffine ((𝒰' i).obj j)),
          ∀ i j k, P (pullback.map_desc ((𝒰' i).map j) ((𝒰' i).map k) pullback.snd)] := by
  tfae_have 1 → 4
  · introv H hU hg _ _; skip; apply P.diagonal_of_target_affine_locally <;> assumption
  tfae_have 4 → 3
  · introv H h𝒰; skip; apply H
  tfae_have 3 → 2
  · exact fun H => ⟨Y.affine_cover, inferInstance, H Y.affine_cover⟩
  tfae_have 2 → 5
  · rintro ⟨𝒰, h𝒰, H⟩
    skip
    refine' ⟨𝒰, inferInstance, fun _ => Scheme.affine_cover _, inferInstance, _⟩
    intro i j k
    apply H
  tfae_have 5 → 1
  · rintro ⟨𝒰, _, 𝒰', _, H⟩
    exact diagonal_target_affine_locally_of_open_cover P hP f 𝒰 𝒰' H
  tfae_finish
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal_affine_open_cover_tfae AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.diagonal_affine_openCover_tFAE

theorem AffineTargetMorphismProperty.IsLocal.diagonal {P : AffineTargetMorphismProperty}
    (hP : P.IsLocal) : P.diagonal.IsLocal :=
  AffineTargetMorphismProperty.isLocalOfOpenCoverImply P.diagonal (P.diagonal_respectsIso hP.1)
    fun _ _ f => ((hP.diagonal_affine_openCover_tFAE f).out 1 3).mp
#align algebraic_geometry.affine_target_morphism_property.is_local.diagonal AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.diagonal

theorem diagonal_targetAffineLocally_eq_targetAffineLocally (P : AffineTargetMorphismProperty)
    (hP : P.IsLocal) : (targetAffineLocally P).diagonal = targetAffineLocally P.diagonal := by
  ext _ _ f
  exact
    ((hP.diagonal_affine_open_cover_tfae f).out 0 1).trans
      ((hP.diagonal.affine_open_cover_tfae f).out 1 0)
#align algebraic_geometry.diagonal_target_affine_locally_eq_target_affine_locally AlgebraicGeometry.diagonal_targetAffineLocally_eq_targetAffineLocally

theorem universallyIsLocalAtTarget (P : MorphismProperty Scheme)
    (hP :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y),
        (∀ i : 𝒰.J, P (pullback.snd : (𝒰.pullbackCover f).obj i ⟶ 𝒰.obj i)) → P f) :
    PropertyIsLocalAtTarget P.universally := by
  refine'
    ⟨P.universally_respects_iso, fun X Y f U =>
      P.universally_stable_under_base_change (is_pullback_morphism_restrict f U).flip, _⟩
  intro X Y f 𝒰 h X' Y' i₁ i₂ f' H
  apply hP _ (𝒰.pullback_cover i₂)
  intro i
  dsimp
  apply h i (pullback.lift (pullback.fst ≫ i₁) (pullback.snd ≫ pullback.snd) _) pullback.snd
  swap
  · rw [category.assoc, category.assoc, ← pullback.condition, ← pullback.condition_assoc, H.w]
  refine' (is_pullback.of_right _ (pullback.lift_snd _ _ _) (is_pullback.of_has_pullback _ _)).flip
  rw [pullback.lift_fst, ← pullback.condition]
  exact (is_pullback.of_has_pullback _ _).paste_horiz H.flip
#align algebraic_geometry.universally_is_local_at_target AlgebraicGeometry.universallyIsLocalAtTarget

theorem universallyIsLocalAtTargetOfMorphismRestrict (P : MorphismProperty Scheme)
    (hP₁ : P.RespectsIso)
    (hP₂ :
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type u} (U : ι → Opens Y.carrier) (hU : iSup U = ⊤),
        (∀ i, P (f ∣_ U i)) → P f) :
    PropertyIsLocalAtTarget P.universally :=
  universallyIsLocalAtTarget P
    (by
      intro X Y f 𝒰 h𝒰
      apply hP₂ f (fun i : 𝒰.J => (𝒰.map i).opensRange) 𝒰.supr_opens_range
      simp_rw [hP₁.arrow_mk_iso_iff (morphism_restrict_opens_range f _)]
      exact h𝒰)
#align algebraic_geometry.universally_is_local_at_target_of_morphism_restrict AlgebraicGeometry.universallyIsLocalAtTargetOfMorphismRestrict

/-- `topologically P` holds for a morphism if the underlying topological map satisfies `P`. -/
def MorphismProperty.topologically
    (P : ∀ {α β : Type u} [TopologicalSpace α] [TopologicalSpace β] (f : α → β), Prop) :
    MorphismProperty Scheme.{u} := fun X Y f => P f.1.base
#align algebraic_geometry.morphism_property.topologically AlgebraicGeometry.MorphismProperty.topologically

end AlgebraicGeometry


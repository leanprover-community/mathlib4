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


universe u

open CategoryTheory Opposite TopologicalSpace CategoryTheory.Limits AlgebraicGeometry

variable (P : ∀ {R S : Type u} [CommRing R] [CommRing S], (R →+* S) → Prop)

namespace RingHom

variable {P}
theorem RespectsIso.basicOpen_iff (hP : RespectsIso @P) {X Y : Scheme} [IsAffine X] [IsAffine Y]
    (f : X ⟶ Y) (r : Y.presheaf.obj (Opposite.op ⊤)) :
    P (Scheme.Γ.map (f ∣_ Y.basicOpen r).op) ↔
    P (@IsLocalization.Away.map (Y.presheaf.obj (Opposite.op ⊤)) _
      (Y.presheaf.obj (Opposite.op <| Y.basicOpen r)) _ _ (X.presheaf.obj (Opposite.op ⊤)) _
      (X.presheaf.obj (Opposite.op <| X.basicOpen (Scheme.Γ.map f.op r))) _ _
      (Scheme.Γ.map f.op) r _ <| @isLocalization_away_of_isAffine X _ (Scheme.Γ.map f.op r)) := by
  rw [Γ_map_morphismRestrict, hP.cancel_left_isIso, hP.cancel_right_isIso,
    ← hP.cancel_right_isIso (f.val.c.app (Opposite.op (Y.basicOpen r)))
      (X.presheaf.map (eqToHom (Scheme.preimage_basicOpen f r).symm).op), ← eq_iff_iff]
  congr
  delta IsLocalization.Away.map
  refine' IsLocalization.ringHom_ext (Submonoid.powers r) _
  generalize_proofs h1 h2 h3
  haveI i1 := @isLocalization_away_of_isAffine X _ (Scheme.Γ.map f.op r)
  -- Porting note: needs to be very explicit here
  convert
    (@IsLocalization.map_comp (hy := h3) (Y.presheaf.obj <| Opposite.op (Scheme.basicOpen Y r))
    _ _ (isLocalization_away_of_isAffine _) _ _ _ i1).symm using 1
  change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _
  rw [f.val.c.naturality_assoc]
  erw [← X.presheaf.map_comp]
  congr 1
#align ring_hom.respects_iso.basic_open_iff RingHom.RespectsIso.basicOpen_iff

theorem RespectsIso.basicOpen_iff_localization (hP : RespectsIso @P) {X Y : Scheme} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (Opposite.op ⊤)) :
    P (Scheme.Γ.map (f ∣_ Y.basicOpen r).op) ↔ P (Localization.awayMap (Scheme.Γ.map f.op) r) := by
  refine (hP.basicOpen_iff _ _).trans ?_
  -- Porting note: was a one line term mode proof, but this `dsimp` is vital so the term mode
  -- one liner is not possible
  dsimp
  rw [← hP.is_localization_away_iff]
#align ring_hom.respects_iso.basic_open_iff_localization RingHom.RespectsIso.basicOpen_iff_localization

@[deprecated] alias RespectsIso.ofRestrict_morphismRestrict_iff_of_isAffine :=
  RespectsIso.basicOpen_iff_localization

theorem RespectsIso.ofRestrict_morphismRestrict_iff (hP : RingHom.RespectsIso @P) {X Y : Scheme}
    [IsAffine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (Opposite.op ⊤)) (U : Opens X.carrier)
    (hU : IsAffineOpen U) {V : Opens _}
    (e : V = (Scheme.ιOpens <| f ⁻¹ᵁ Y.basicOpen r) ⁻¹ᵁ U) :
    P (Scheme.Γ.map (Scheme.ιOpens V ≫ f ∣_ Y.basicOpen r).op) ↔
    P (Localization.awayMap (Scheme.Γ.map (Scheme.ιOpens U ≫ f).op) r) := by
  subst e
  refine (hP.cancel_right_isIso _
    (Scheme.Γ.mapIso (Scheme.restrictRestrictComm _ _ _).op).inv).symm.trans ?_
  haveI : IsAffine _ := hU
  rw [← hP.basicOpen_iff_localization, iff_iff_eq]
  congr 1
  simp only [Functor.mapIso_inv, Iso.op_inv, ← Functor.map_comp, ← op_comp, morphismRestrict_comp]
  rw [← Category.assoc]
  congr 3
  rw [← cancel_mono (Scheme.ιOpens _), Category.assoc, Scheme.restrictRestrictComm,
    IsOpenImmersion.isoOfRangeEq_inv_fac, morphismRestrict_ι]
#align ring_hom.respects_iso.of_restrict_morphism_restrict_iff RingHom.RespectsIso.ofRestrict_morphismRestrict_iff

theorem StableUnderBaseChange.Γ_pullback_fst (hP : StableUnderBaseChange @P) (hP' : RespectsIso @P)
    {X Y S : Scheme} [IsAffine X] [IsAffine Y] [IsAffine S] (f : X ⟶ S) (g : Y ⟶ S)
    (H : P (Scheme.Γ.map g.op)) : P (Scheme.Γ.map (pullback.fst : pullback f g ⟶ _).op) := by
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
  rw [← this, hP'.cancel_right_isIso,
    ← pushoutIsoUnopPullback_inl_hom (Quiver.Hom.unop _) (Quiver.Hom.unop _),
    hP'.cancel_right_isIso]
  exact hP.pushout_inl _ hP' _ _ H
#align ring_hom.stable_under_base_change.Γ_pullback_fst RingHom.StableUnderBaseChange.Γ_pullback_fst

end RingHom

namespace AlgebraicGeometry

/-- For `P` a property of ring homomorphisms, `sourceAffineLocally P` holds for `f : X ⟶ Y`
whenever `P` holds for the restriction of `f` on every affine open subset of `X`. -/
def sourceAffineLocally : AffineTargetMorphismProperty := fun X _ f _ =>
  ∀ U : X.affineOpens, P (Scheme.Γ.map (X.ofRestrict U.1.openEmbedding ≫ f).op)
#align algebraic_geometry.source_affine_locally AlgebraicGeometry.sourceAffineLocally

/-- For `P` a property of ring homomorphisms, `affineLocally P` holds for `f : X ⟶ Y` if for each
affine open `U = Spec A ⊆ Y` and `V = Spec B ⊆ f ⁻¹' U`, the ring hom `A ⟶ B` satisfies `P`.
Also see `affineLocally_iff_affineOpens_le`. -/
abbrev affineLocally : MorphismProperty Scheme :=
  targetAffineLocally (sourceAffineLocally @P)
#align algebraic_geometry.affine_locally AlgebraicGeometry.affineLocally

variable {P}

theorem sourceAffineLocally_respectsIso (h₁ : RingHom.RespectsIso @P) :
    (sourceAffineLocally @P).toProperty.RespectsIso := by
  apply AffineTargetMorphismProperty.respectsIso_mk
  · introv H U
    rw [← h₁.cancel_right_isIso _ (Scheme.Γ.map (Scheme.restrictMapIso e.inv U.1).hom.op), ←
      Functor.map_comp, ← op_comp]
    convert H ⟨_, U.prop.map_isIso e.inv⟩ using 3
    -- Porting note: have to add this instance manually
    haveI i1 : IsOpenImmersion
      (Scheme.ofRestrict Y ((Opens.map e.inv.val.base).obj U.1).openEmbedding ≫ e.inv) :=
      PresheafedSpace.IsOpenImmersion.comp _ _
    rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc, Category.assoc,
      e.inv_hom_id_assoc]
  · introv H U
    rw [← Category.assoc, op_comp, Functor.map_comp, h₁.cancel_left_isIso]
    exact H U
#align algebraic_geometry.source_affine_locally_respects_iso AlgebraicGeometry.sourceAffineLocally_respectsIso

theorem affineLocally_respectsIso (h : RingHom.RespectsIso @P) : (affineLocally @P).RespectsIso :=
  targetAffineLocally_respectsIso (sourceAffineLocally_respectsIso h)
#align algebraic_geometry.affine_locally_respects_iso AlgebraicGeometry.affineLocally_respectsIso

theorem affineLocally_iff_affineOpens_le (hP : RingHom.RespectsIso @P) {X Y : Scheme} (f : X ⟶ Y) :
    affineLocally (@P) f ↔
    ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ (Opens.map f.1.base).obj U.1),
      P (Scheme.Hom.appLe f e) := by
  apply forall_congr'
  intro U
  delta sourceAffineLocally
  simp_rw [op_comp, Scheme.Γ.map_comp, Γ_map_morphismRestrict, Category.assoc, Scheme.Γ_map_op,
    hP.cancel_left_isIso]
  constructor
  · intro H V e
    let U' := (Opens.map f.val.base).obj U.1
    have e' : U'.openEmbedding.isOpenMap.functor.obj ((Opens.map U'.inclusion).obj V.1) = V.1 := by
      ext1; refine' Set.image_preimage_eq_inter_range.trans (Set.inter_eq_left.mpr _)
      erw [Subtype.range_val]
      convert e
    have := H ⟨(Opens.map (X.ofRestrict U'.openEmbedding).1.base).obj V.1, ?h'⟩
    erw [← X.presheaf.map_comp] at this
    rw [← hP.cancel_right_isIso _ (X.presheaf.map (eqToHom _)), Category.assoc,
      ← X.presheaf.map_comp]
    convert this using 1
    dsimp only [Functor.op, unop_op]
    rw [Opens.openEmbedding_obj_top]
    congr 1
    exact e'.symm
    case h' =>
      apply (X.ofRestrict U'.openEmbedding).isAffineOpen_iff_of_isOpenImmersion.mp
      -- Porting note: was convert V.2
      erw [e']
      apply V.2
  · intro H V
    specialize H ⟨_, V.2.imageIsOpenImmersion (X.ofRestrict _)⟩ (Subtype.coe_image_subset _ _)
    erw [← X.presheaf.map_comp]
    rw [← hP.cancel_right_isIso _ (X.presheaf.map (eqToHom _)), Category.assoc, ←
      X.presheaf.map_comp]
    convert H
    · dsimp only [Functor.op, unop_op]; rw [Opens.openEmbedding_obj_top]
#align algebraic_geometry.affine_locally_iff_affine_opens_le AlgebraicGeometry.affineLocally_iff_affineOpens_le

theorem scheme_restrict_basicOpen_of_localizationPreserves (h₁ : RingHom.RespectsIso @P)
    (h₂ : RingHom.LocalizationPreserves @P) {X Y : Scheme} [IsAffine Y] (f : X ⟶ Y)
    (r : Y.presheaf.obj (op ⊤)) (H : sourceAffineLocally (@P) f)
    (U : (X.restrict ((Opens.map f.1.base).obj <| Y.basicOpen r).openEmbedding).affineOpens) :
    P (Scheme.Γ.map ((X.restrict ((Opens.map f.1.base).obj <|
      Y.basicOpen r).openEmbedding).ofRestrict U.1.openEmbedding ≫ f ∣_ Y.basicOpen r).op) := by
  specialize H ⟨_, U.2.imageIsOpenImmersion (X.ofRestrict _)⟩
  letI i1 : Algebra (Y.presheaf.obj <| Opposite.op ⊤) (Localization.Away r) := Localization.algebra
  exact (h₁.ofRestrict_morphismRestrict_iff f r
    ((Scheme.Hom.opensFunctor
      (X.ofRestrict ((Opens.map f.1.base).obj <| Y.basicOpen r).openEmbedding)).obj U.1)
    (IsAffineOpen.imageIsOpenImmersion U.2
      (X.ofRestrict ((Opens.map f.1.base).obj <| Y.basicOpen r).openEmbedding))
    (Opens.ext (Set.preimage_image_eq _ Subtype.coe_injective).symm)).mpr (h₂.away r H)
set_option linter.uppercaseLean3 false in
#align algebraic_geometry.Scheme_restrict_basic_open_of_localization_preserves AlgebraicGeometry.scheme_restrict_basicOpen_of_localizationPreserves

theorem sourceAffineLocally_isLocal (h₁ : RingHom.RespectsIso @P)
    (h₂ : RingHom.LocalizationPreserves @P) (h₃ : RingHom.OfLocalizationSpan @P) :
    (sourceAffineLocally @P).IsLocal := by
  constructor
  · exact sourceAffineLocally_respectsIso h₁
  · introv H U
    apply scheme_restrict_basicOpen_of_localizationPreserves h₁ h₂; assumption
  · introv hs hs' U
    skip
    apply h₃ _ _ hs
    intro r
    have := hs' r ⟨(Opens.map (X.ofRestrict _).1.base).obj U.1, ?_⟩
    rwa [h₁.ofRestrict_morphismRestrict_iff] at this
    · exact U.2
    · rfl
    · suffices ∀ (V) (_ : V = (Opens.map f.val.base).obj (Y.basicOpen r.val)),
          IsAffineOpen ((Opens.map (X.ofRestrict V.openEmbedding).1.base).obj U.1) by
        exact this _ rfl
      intro V hV
      rw [Scheme.preimage_basicOpen] at hV
      subst hV
      exact U.2.mapRestrictBasicOpen (Scheme.Γ.map f.op r.1)
#align algebraic_geometry.source_affine_locally_is_local AlgebraicGeometry.sourceAffineLocally_isLocal

variable (hP : RingHom.PropertyIsLocal @P)

theorem sourceAffineLocally_of_source_open_cover_aux (h₁ : RingHom.RespectsIso @P)
    (h₃ : RingHom.OfLocalizationSpanTarget @P) {X Y : Scheme} (f : X ⟶ Y) (U : X.affineOpens)
    (s : Set (X.presheaf.obj (op U.1))) (hs : Ideal.span s = ⊤)
    (hs' : ∀ r : s, P (Scheme.Γ.map (Scheme.ιOpens (X.basicOpen r.1) ≫ f).op)) :
    P (Scheme.Γ.map (Scheme.ιOpens U ≫ f).op) := by
  apply_fun Ideal.map (X.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op) at hs
  rw [Ideal.map_span, Ideal.map_top] at hs
  apply h₃.ofIsLocalization h₁ _ _ hs
  rintro ⟨s, r, hr, hs⟩
  refine ⟨_, _, _, @AlgebraicGeometry.Γ_restrict_isLocalization (X ∣_ᵤ U.1) U.2 s, ?_⟩
  rw [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_eq_ring_hom_comp, ← Functor.map_comp,
    ← op_comp, ← h₁.cancel_right_isIso _ (Scheme.Γ.mapIso (Scheme.restrictRestrict _ _ _).op).inv]
  subst hs
  rw [← h₁.cancel_right_isIso _
    (Scheme.Γ.mapIso (Scheme.restrictIsoOfEq _ (Scheme.map_basicOpen_map _ _ _)).op).inv]
  simp only [Functor.mapIso_inv, Iso.op_inv, ← Functor.map_comp, ← op_comp,
    Scheme.restrictRestrict_inv_restrict_restrict_assoc, Scheme.restrictIsoOfEq,
    IsOpenImmersion.isoOfRangeEq_inv_fac_assoc]
  exact hs' ⟨r, hr⟩
#align algebraic_geometry.source_affine_locally_of_source_open_cover_aux AlgebraicGeometry.sourceAffineLocally_of_source_open_cover_aux

theorem isOpenImmersionCat_comp_of_sourceAffineLocally (h₁ : RingHom.RespectsIso @P)
    {X Y Z : Scheme} [IsAffine X] [IsAffine Z] (f : X ⟶ Y) [IsOpenImmersion f] (g : Y ⟶ Z)
    (h₂ : sourceAffineLocally (@P) g) : P (Scheme.Γ.map (f ≫ g).op) := by
  rw [← h₁.cancel_right_isIso _
    (Scheme.Γ.map (IsOpenImmersion.isoOfRangeEq (Y.ofRestrict _) f _).hom.op),
    ← Functor.map_comp, ← op_comp]
  convert h₂ ⟨_, rangeIsAffineOpenOfOpenImmersion f⟩ using 3
  · rw [IsOpenImmersion.isoOfRangeEq_hom_fac_assoc]
    exact Subtype.range_coe
#align algebraic_geometry.is_open_immersion_comp_of_source_affine_locally AlgebraicGeometry.isOpenImmersionCat_comp_of_sourceAffineLocally

end AlgebraicGeometry

open AlgebraicGeometry

namespace RingHom.PropertyIsLocal

variable {P} (hP : RingHom.PropertyIsLocal @P)

theorem sourceAffineLocally_of_source_openCover {X Y : Scheme} (f : X ⟶ Y) [IsAffine Y]
    (𝒰 : X.OpenCover) [∀ i, IsAffine (𝒰.obj i)] (H : ∀ i, P (Scheme.Γ.map (𝒰.map i ≫ f).op)) :
    sourceAffineLocally (@P) f := by
  let S i := (⟨⟨Set.range (𝒰.map i).1.base, (𝒰.IsOpen i).base_open.open_range⟩,
    rangeIsAffineOpenOfOpenImmersion (𝒰.map i)⟩ : X.affineOpens)
  intro U
  -- Porting note: here is what we are eliminating into Lean
  apply of_affine_open_cover
    (P := fun V => P (Scheme.Γ.map (X.ofRestrict (Opens.openEmbedding V.val) ≫ f).op)) U
  pick_goal 5
  · exact Set.range S
  · intro U r H
    -- Porting note: failing on instance synthesis for an (unspecified) meta variable
    -- made φ explicit and forced to use dsimp in the proof
    convert hP.StableUnderComposition
      (S := Scheme.Γ.obj (Opposite.op (X.restrict <| Opens.openEmbedding U.val)))
      (T := Scheme.Γ.obj (Opposite.op (X.restrict <| Opens.openEmbedding (X.basicOpen r))))
      ?_ ?_ H ?_ using 1
    swap
    · refine' X.presheaf.map
          (@homOfLE _ _ ((IsOpenMap.functor _).obj _) ((IsOpenMap.functor _).obj _) _).op
      rw [unop_op, unop_op, Opens.openEmbedding_obj_top, Opens.openEmbedding_obj_top]
      exact X.basicOpen_le _
    · rw [op_comp, op_comp, Functor.map_comp, Functor.map_comp]
      refine' (Eq.trans _ (Category.assoc (obj := CommRingCat) _ _ _).symm : _)
      congr 1
      dsimp
      refine' Eq.trans _ (X.presheaf.map_comp _ _)
      change X.presheaf.map _ = _
      congr!
    -- Porting note: need to pass Algebra through explicitly
    convert @HoldsForLocalizationAway _ hP _
      (Scheme.Γ.obj (Opposite.op (X.restrict (X.basicOpen r).openEmbedding))) _ _ ?_
      (X.presheaf.map (eqToHom U.1.openEmbedding_obj_top).op r) ?_
    · exact RingHom.algebraMap_toAlgebra
        (R := Scheme.Γ.obj <| Opposite.op <| X.restrict (U.1.openEmbedding))
        (S :=
          Scheme.Γ.obj (Opposite.op <| X.restrict (X.affineBasicOpen r).1.openEmbedding)) _|>.symm
    · dsimp [Scheme.Γ]
      have := U.2
      rw [← U.1.openEmbedding_obj_top] at this
      -- Porting note: the second argument of `IsLocalization.Away` is a type, and we want
      -- to generate an equality, so using `typeEqs := true` to force allowing type equalities.
      convert (config := {typeEqs := true, transparency := .default})
          this.isLocalization_basicOpen _ using 5
      all_goals rw [Opens.openEmbedding_obj_top]; exact (Scheme.basicOpen_res_eq _ _ _).symm
  · introv hs hs'
    exact sourceAffineLocally_of_source_open_cover_aux hP.respectsIso hP.2 _ _ _ hs hs'
  · rw [Set.eq_univ_iff_forall]
    intro x
    rw [Set.mem_iUnion]
    exact ⟨⟨_, 𝒰.f x, rfl⟩, 𝒰.Covers x⟩
  · rintro ⟨_, i, rfl⟩
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
  tfae
    1 → 4
    | H, U, g, _, hg => by
      skip
      specialize H ⟨⟨_, hg.base_open.open_range⟩, rangeIsAffineOpenOfOpenImmersion g⟩
      rw [← hP.respectsIso.cancel_right_isIso _ (Scheme.Γ.map (IsOpenImmersion.isoOfRangeEq g
        (X.ofRestrict (Opens.openEmbedding ⟨_, hg.base_open.open_range⟩))
        Subtype.range_coe.symm).hom.op),
        ← Scheme.Γ.map_comp, ← op_comp, IsOpenImmersion.isoOfRangeEq_hom_fac_assoc] at H
      exact H
    4 → 3
    | H, 𝒰, _, i => by skip; apply H
    3 → 2
    | H => by refine' ⟨X.affineCover, inferInstance, H _⟩
    2 → 1 := by
      rintro ⟨𝒰, _, h𝒰⟩
      exact sourceAffineLocally_of_source_openCover hP f 𝒰 h𝒰
#align ring_hom.property_is_local.affine_open_cover_tfae RingHom.PropertyIsLocal.affine_openCover_TFAE

theorem openCover_TFAE {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) :
    List.TFAE
      [sourceAffineLocally (@P) f,
        ∃ 𝒰 : Scheme.OpenCover.{u} X, ∀ i : 𝒰.J, sourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ (𝒰 : Scheme.OpenCover.{u} X) (i : 𝒰.J), sourceAffineLocally (@P) (𝒰.map i ≫ f),
        ∀ {U : Scheme} (g : U ⟶ X) [IsOpenImmersion g], sourceAffineLocally (@P) (g ≫ f)] := by
  tfae
    1 → 4
    | H, U, g, hg, V => by
      skip
      -- Porting note: this has metavariable if I put it directly into rw
      have := (hP.affine_openCover_TFAE f).out 0 3
      rw [this] at H
      haveI : IsAffine _ := V.2
      rw [← Category.assoc]
      -- Porting note: Lean could find this previously
      have : IsOpenImmersion <| (Scheme.ofRestrict U (Opens.openEmbedding V.val)) ≫ g :=
        LocallyRingedSpace.IsOpenImmersion.comp _ _
      apply H
    4 → 3
    | H, 𝒰, _, i => by skip; apply H
    3 → 2
    | H => by refine' ⟨X.affineCover, H _⟩
    2 → 1 := by
      rintro ⟨𝒰, h𝒰⟩
      -- Porting note: this has metavariable if I put it directly into rw
      have := (hP.affine_openCover_TFAE f).out 0 1
      rw [this]
      refine' ⟨𝒰.bind fun _ => Scheme.affineCover _, _, _⟩
      · intro i; dsimp; infer_instance
      · intro i
        specialize h𝒰 i.1
        -- Porting note: this has metavariable if I put it directly into rw
        have := (hP.affine_openCover_TFAE (𝒰.map i.fst ≫ f)).out 0 3
        rw [this] at h𝒰
        erw [Category.assoc]
        -- Porting note: this was discharged after the apply previously
        have : IsAffine (Scheme.OpenCover.obj
          (Scheme.OpenCover.bind 𝒰 fun x ↦ Scheme.affineCover (Scheme.OpenCover.obj 𝒰 x)) i) := by
            dsimp; infer_instance
        apply @h𝒰 _ (show _ from _)
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

theorem is_local_affineLocally : PropertyIsLocalAtTarget (affineLocally @P) :=
  hP.isLocal_sourceAffineLocally.targetAffineLocallyIsLocal
#align ring_hom.property_is_local.is_local_affine_locally RingHom.PropertyIsLocal.is_local_affineLocally

theorem affine_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} Y)
    [∀ i, IsAffine (𝒰.obj i)] (𝒰' : ∀ i, Scheme.OpenCover.{u} ((𝒰.pullbackCover f).obj i))
    [∀ i j, IsAffine ((𝒰' i).obj j)] :
    affineLocally (@P) f ↔ ∀ i j, P (Scheme.Γ.map ((𝒰' i).map j ≫ pullback.snd).op) :=
  (hP.isLocal_sourceAffineLocally.affine_openCover_iff f 𝒰).trans
    (forall_congr' fun i => hP.source_affine_openCover_iff _ (𝒰' i))
#align ring_hom.property_is_local.affine_open_cover_iff RingHom.PropertyIsLocal.affine_openCover_iff

-- Porting note: doesn't build without the `IsAffine` instance but the linter complains
@[nolint unusedHavesSuffices]
theorem source_openCover_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (𝒰 : Scheme.OpenCover.{u} X) :
    affineLocally (@P) f ↔ ∀ i, affineLocally (@P) (𝒰.map i ≫ f) := by
  constructor
  · intro H i U
    rw [morphismRestrict_comp]
    delta morphismRestrict
    -- Porting note: Lean can no longer find these instances for the following apply
    have : IsAffine (Scheme.restrict Y <| Opens.openEmbedding U.val) := U.property
    have : IsOpenImmersion ((pullbackRestrictIsoRestrict (Scheme.OpenCover.map 𝒰 i)
        ((Opens.map f.val.base).obj ↑U)).inv ≫ pullback.snd) :=
      LocallyRingedSpace.IsOpenImmersion.comp _ _
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
    rw [Category.assoc, affine_cancel_left_isIso this, ←
      affine_cancel_left_isIso this (pullbackSymmetry _ _).hom,
      pullbackSymmetry_hom_comp_snd_assoc] at H
    exact H
#align ring_hom.property_is_local.source_open_cover_iff RingHom.PropertyIsLocal.source_openCover_iff

theorem affineLocally_of_isOpenImmersion (hP : RingHom.PropertyIsLocal @P) {X Y : Scheme}
    (f : X ⟶ Y) [hf : IsOpenImmersion f] : affineLocally (@P) f := by
  intro U
  haveI H : IsAffine _ := U.2
  rw [← Category.comp_id (f ∣_ U)]
  apply hP.sourceAffineLocally_comp_of_isOpenImmersion
  -- Porting note: need to excuse Lean from synthesizing an instance
  rw [@source_affine_openCover_iff _ hP _ _ _ _ (Scheme.openCoverOfIsIso (𝟙 _)) (_)]
  · intro i; erw [Category.id_comp, op_id, Scheme.Γ.map_id]
    let esto := Scheme.Γ.obj (Opposite.op (Y.restrict <| Opens.openEmbedding U.val))
    let eso := Scheme.Γ.obj (Opposite.op ((Scheme.openCoverOfIsIso
      (𝟙 (Y.restrict <| Opens.openEmbedding U.val))).obj i))
    -- Porting note: Lean this needed this spelled out before
    -- convert hP.HoldsAwayLocalizationAway _ (1 : Scheme.Γ.obj _) _
    have : 𝟙 (Scheme.Γ.obj (Opposite.op (Y.restrict <| Opens.openEmbedding U.val)))
      = @algebraMap esto eso _ _ (_) := (RingHom.algebraMap_toAlgebra _).symm
    rw [this]
    have := hP.HoldsForLocalizationAway
    convert @this esto eso _ _ ?_ ?_ ?_
    · exact 1
    -- Porting note: again we have to bypass TC synthesis to keep Lean from running away
    · refine'
        @IsLocalization.away_of_isUnit_of_bijective _ _ _ _ (_) _ isUnit_one Function.bijective_id
  · intro; exact H
#align ring_hom.property_is_local.affine_locally_of_is_open_immersion RingHom.PropertyIsLocal.affineLocally_of_isOpenImmersion

theorem affineLocally_of_comp
    (H : ∀ {R S T : Type u} [CommRing R] [CommRing S] [CommRing T],
      ∀ (f : R →+* S) (g : S →+* T), P (g.comp f) → P g)
    {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} (h : affineLocally (@P) (f ≫ g)) :
    affineLocally (@P) f := by
  let 𝒰 : ∀ i, ((Z.affineCover.pullbackCover (f ≫ g)).obj i).OpenCover := by
    intro i
    refine' Scheme.OpenCover.bind _ fun i => Scheme.affineCover _
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
  -- Porting note: this previously ended with `exact H _ _ h` but that runs away
  -- explicitly specifying `f'` and `g'` in the `comp` and then using a `convert` (?)
  -- lets us get something
  let f' := Scheme.Γ.map (Scheme.OpenCover.map
      (Scheme.affineCover (pullback g (Scheme.OpenCover.map (Scheme.affineCover Z) i))) j ≫
        pullback.snd).op
  let g' := Scheme.Γ.map (Scheme.OpenCover.map (Scheme.affineCover (pullback f
      (Scheme.OpenCover.map (Scheme.affineCover (pullback g (Scheme.OpenCover.map
        (Scheme.affineCover Z) i))) j ≫ pullback.fst))) k ≫ pullback.snd).op
  convert H f' g' ?_
  exact h
#align ring_hom.property_is_local.affine_locally_of_comp RingHom.PropertyIsLocal.affineLocally_of_comp

theorem affineLocally_stableUnderComposition : (affineLocally @P).StableUnderComposition := by
  intro X Y S f g hf hg
  let 𝒰 : ∀ i, ((S.affineCover.pullbackCover (f ≫ g)).obj i).OpenCover := by
    intro i
    refine' Scheme.OpenCover.bind _ fun i => Scheme.affineCover _
    apply Scheme.OpenCover.pushforwardIso _
      (pullbackRightPullbackFstIso g (S.affineCover.map i) f).hom
    apply Scheme.Pullback.openCoverOfRight
    exact (pullback g (S.affineCover.map i)).affineCover
  -- Porting note: used to be - rw [hP.affine_openCover_iff (f ≫ g) S.affineCover _] - but
  -- metavariables cause problems in the instance search
  apply (@affine_openCover_iff _ hP _ _ (f ≫ g) S.affineCover _ ?_ ?_).mpr
  rotate_left
  · exact 𝒰
  · intro i j; dsimp [𝒰] at *; infer_instance
  · rintro i ⟨j, k⟩
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
#align ring_hom.property_is_local.affine_locally_stable_under_composition RingHom.PropertyIsLocal.affineLocally_stableUnderComposition

end RingHom.PropertyIsLocal

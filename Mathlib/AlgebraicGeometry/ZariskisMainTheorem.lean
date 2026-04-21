/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.RingTheory.Etale.QuasiFinite

/-!

# Zariski's Main Theorem

In this file we prove Grothendieck's reformulation of Zariski's main theorem, namely if
`f : X ⟶ Y` is separated and of finite type, then the map from the quasi-finite locus `U ⊆ X` of
`f` to the relative normalization `X'` of `Y` in `X` is an open immersion.

We then have the following corollaries
- `Scheme.Hom.isOpen_quasiFiniteAt` : If `f` is separated and of finite type, then the quasi-finite
  locus of `f` is open.
- If `f` is itself quasi-finite, then the map `f.toNormalization : X ⟶ X'` is an open immersion.
  This can be accessed via `inferInstance`.
- `IsFinite.of_isProper_of_locallyQuasiFinite`:
  If `f` is proper and quasi-finite, then the map `f.toNormalization : X ⟶ X'` is an isomorphism,
  which implies that `f` itself is finite.

-/
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits

@[expose] public section

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]

set_option backward.isDefEq.respectTransparency false in
open TensorProduct in
-- Note: This is weaker than stacks#02LN but is enough to proof Zariski's main.
-- TODO: generalize this.
theorem exists_etale_isCompl_of_quasiFiniteAt [IsSeparated f]
    {x : X} {s : S} (h : f x = s) (hx : f.QuasiFiniteAt x) :
    ∃ (U : Scheme) (g : U ⟶ S), Etale g ∧ s ∈ Set.range g ∧
    ∃ (V W : (pullback f g).Opens) (v : V), IsCompl V W ∧ IsFinite (V.ι ≫ pullback.snd f g) ∧
      pullback.fst f g v.1 = x := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (f x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hUV : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).2
  have : (f.appLE U V hUV).hom.FiniteType := f.finiteType_appLE hU hV hUV
  algebraize [(f.appLE U V hUV).hom]
  have : (hV.primeIdealOf ⟨x, hxV⟩).asIdeal.LiesOver (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal := by
    suffices hU.primeIdealOf ⟨f x, hxU⟩ = Spec.map (f.appLE U V hUV) (hV.primeIdealOf ⟨x, hxV⟩) from
      ⟨congr(($this).1)⟩
    apply hU.isoSpec.inv.homeomorph.injective
    apply Subtype.ext
    simp only [IsAffineOpen.primeIdealOf, Scheme.Hom.homeomorph_apply,
      ← Scheme.Hom.comp_apply, ← Scheme.Opens.ι_apply, IsAffineOpen.isoSpec_hom]
    simp
  have : Algebra.QuasiFiniteAt Γ(S, U) (hV.primeIdealOf ⟨x, hxV⟩).asIdeal :=
    hx.quasiFiniteAt hV hU hUV hxV
  obtain ⟨R, _, _, _, P, _, _, e, _, P', _, _, hP', heP', -, _, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq
    (hU.primeIdealOf ⟨f x, hxU⟩).asIdeal (hV.primeIdealOf ⟨x, hxV⟩).asIdeal
  have : (algebraMap R (Localization.Away e)).Finite := RingHom.finite_algebraMap.mpr ‹_›
  let φ : Γ(S, U) ⟶ .of R := CommRingCat.ofHom <| algebraMap Γ(S, U) R
  have hφ : φ.hom.Etale := RingHom.etale_algebraMap.mpr ‹_›
  have : Etale (Spec.map φ) := HasRingHomProperty.Spec_iff.mpr hφ
  let e₁ : Spec (.of (R ⊗ Γ(X, V))) ≅ pullback (Spec.map (f.appLE U V hUV)) (Spec.map φ) :=
    (pullbackSpecIso _ _ _).symm ≪≫ pullbackSymmetry _ _
  have he₁ : e₁.hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom) := by
    dsimp [e₁, RingHom.algebraMap_toAlgebra]
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst]
    exact pullbackSpecIso_inv_snd ..
  let g : Spec (.of (R ⊗[Γ(S, U)] Γ(X, V))) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
    e₁.hom ≫ pullback.map _ _ _ _ hV.fromSpec (𝟙 _) hU.fromSpec
      (IsAffineOpen.SpecMap_appLE_fromSpec ..) (by simp)
  let W₁ := g ''ᵁ PrimeSpectrum.basicOpen e
  have : IsFinite (W₁.ι ≫ pullback.snd f _) := by
    let ι : Spec (.of (Localization.Away e)) ⟶ pullback f (Spec.map φ ≫ hU.fromSpec) :=
      Spec.map (CommRingCat.ofHom <| algebraMap _ _) ≫ g
    have : ι.opensRange = W₁ := by
      simp only [Scheme.Hom.opensRange_comp, ι, W₁]
      congr 1
      exact TopologicalSpace.Opens.ext <| PrimeSpectrum.localization_away_comap_range _ _
    rw [← this, ← MorphismProperty.cancel_left_of_respectsIso @IsFinite
      (Scheme.Hom.isoOpensRange _).hom]
    have H : (pullbackSpecIso _ R _).inv ≫ pullback.fst _ (Spec.map (f.appLE U V hUV)) = _ :=
      pullbackSpecIso_inv_fst ..
    simpa [Scheme.Hom.isoOpensRange, ι, g, e₁, RingHom.algebraMap_toAlgebra, φ, H,
      ← Spec.map_comp, IsFinite.SpecMap_iff]
  have : IsFinite W₁.ι := .of_comp _ (pullback.snd f _)
  let W₂ : (pullback f (Spec.map φ ≫ hU.fromSpec)).Opens :=
    ⟨W₁ᶜ, by simpa using W₁.ι.isClosedMap.isClosed_range⟩
  refine ⟨Spec (.of R), Spec.map φ ≫ hU.fromSpec, inferInstance,
    ⟨⟨P, ‹_›⟩, ?_⟩, W₁, W₂, ⟨g ⟨P', ‹_›⟩, ?_⟩, ?_, ‹_›, ?_⟩
  · dsimp [Spec.map_apply]
    convert hU.fromSpec_primeIdealOf ⟨f x, hxU⟩
    · exact PrimeSpectrum.ext (Ideal.over_def _ _).symm
    · simp [h]
  · exact ⟨⟨P', ‹_›⟩, heP', rfl⟩
  · simp [isCompl_iff, disjoint_iff, codisjoint_iff, W₂, SetLike.ext'_iff]
  · trans hV.fromSpec ⟨P'.comap Algebra.TensorProduct.includeRight.toRingHom, inferInstance⟩
    · simp [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base, g, reassoc_of% he₁]; rfl
    convert hV.fromSpec_primeIdealOf ⟨x, hxV⟩

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)

set_option backward.isDefEq.respectTransparency false in
lemma Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (x : X) (hx : f.QuasiFiniteAt x) :
    ∃ V, f.toNormalization x ∈ V ∧ IsIso (f.toNormalization ∣_ V) := by
  obtain ⟨T, fT, _, ⟨u, hu⟩, V, W, v, hVW, _, hv₂⟩ := exists_etale_isCompl_of_quasiFiniteAt _ rfl hx
  obtain ⟨U, hU, _⟩ : ∃ U, (pullback.snd f fT).toNormalization v.1 ∈ U ∧
      IsIso ((pullback.snd f fT).toNormalization ∣_ U) := by
    have hVW' : (W : Set ↑(pullback f fT)) = (↑V)ᶜ :=
      eq_compl_iff_isCompl.mpr (hVW.map TopologicalSpace.Opens.frameHom).symm
    have : IsClosedImmersion V.ι := .of_isPreimmersion _ (by simp [eq_compl_comm.mp hVW', W.isOpen])
    have : IsClosedImmersion W.ι := .of_isPreimmersion _ (by simpa [hVW'] using V.2)
    obtain ⟨H⟩ := nonempty_isColimit_binaryCofanMk_of_isCompl V.ι W.ι (by simpa)
    let e : (pullback.snd f fT).normalization ≅ V ⨿ (W.ι ≫ pullback.snd f fT).normalization :=
      (Scheme.Hom.normalizationCoprodIso (pullback.snd f fT) H).symm ≪≫
        coprod.mapIso (asIso (V.ι ≫ pullback.snd f fT).toNormalization).symm (.refl _)
    let ι : V.toScheme ⟶ V ⨿ (W.ι ≫ pullback.snd f fT).normalization := coprod.inl
    refine ⟨e.hom ⁻¹ᵁ ι.opensRange, ⟨v, ?_⟩, ?_⟩
    · rw [← V.ι_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply]
      congr 5
      rw [← Category.assoc, ← Iso.comp_inv_eq]
      simp [ι, e, Scheme.Hom.normalizationCoprodIso]
    rw [← isIso_comp_right_iff _ (e.hom ∣_ ι.opensRange),
      ← morphismRestrict_comp, ← isIso_comp_right_iff _ ι.isoOpensRange.inv]
    have Heq : (pullback.snd f fT).toNormalization ⁻¹ᵁ e.hom ⁻¹ᵁ Scheme.Hom.opensRange ι = V := by
      apply le_antisymm
      · rintro a ⟨b, hab⟩
        by_contra h
        lift a to W using hVW'.ge h
        replace hab : ι b = ((W.ι ≫ pullback.snd f fT).toNormalization ≫ coprod.inr) a := by
          have : W.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inr :=
            H.comp_coconePointUniqueUpToIso_hom _ ⟨.right⟩
          simp only [← W.ι_apply, ← Scheme.Hom.comp_apply, Category.assoc, e] at hab
          simpa [-Scheme.Hom.comp_base, Scheme.Hom.normalizationCoprodIso,
            reassoc_of% this] using hab
        exact Set.disjoint_iff_forall_ne.mp
          (isCompl_range_inl_inr V (W.ι ≫ pullback.snd f fT).normalization).1 ⟨_, rfl⟩ ⟨_, rfl⟩ hab
      · rw [← Scheme.Hom.inv_image, ← SetLike.coe_subset_coe]
        simpa [← Scheme.Hom.opensRange_comp, ι, e, Scheme.Hom.normalizationCoprodIso,
          Set.range_comp] using Set.subset_preimage_image _ _
    convert (inferInstance : IsIso (Scheme.isoOfEq _ Heq).hom)
    rw [Iso.comp_inv_eq, ← Iso.inv_comp_eq, ← cancel_mono (Scheme.Opens.ι _)]
    have : V.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inl :=
      H.comp_coconePointUniqueUpToIso_hom _ ⟨.left⟩
    simp [e, Scheme.Hom.isoOpensRange, Scheme.Hom.normalizationCoprodIso, reassoc_of% this, ι]
  let fTn : (pullback.snd f fT).normalization ⟶ f.normalization :=
    f.normalizationPullback fT ≫ pullback.fst _ _
  let U' : f.normalization.Opens := ⟨_, fTn.isOpenMap _ U.2⟩
  refine ⟨U', ⟨_, hU, by simp only [← hv₂, ← Scheme.Hom.comp_apply]; simp [fTn]⟩, ?_⟩
  let fTnU : U.toScheme ⟶ U' := fTn.resLE _ _ (Set.subset_preimage_image _ _)
  have : Surjective fTnU := ⟨fun ⟨x, a, ha, e⟩ ↦ ⟨⟨a, ha⟩, Subtype.ext <| by simpa [fTnU] using e⟩⟩
  have H : (pullback.snd f fT).toNormalization ⁻¹ᵁ U ≤
      pullback.fst f fT ⁻¹ᵁ f.toNormalization ⁻¹ᵁ U' := by
    refine fun x hx ↦ ⟨_, hx, ?_⟩
    simp only [← Scheme.Hom.comp_apply]
    congr 5
    simp [fTn]
  have : IsPullback ((pullback.snd f fT).toNormalization ∣_ U)
      ((pullback.fst f fT).resLE _ _ H) fTnU (f.toNormalization ∣_ U') := by
    refine .of_bot (t := isPullback_morphismRestrict ..) ?_ ?_
    · simp only [Scheme.Hom.resLE_comp_ι, fTnU]
      refine .paste_vert (isPullback_morphismRestrict ..) ?_
      have H : IsPullback (pullback.map _ _ _ _ f.toNormalization (𝟙 _) (𝟙 _) (by simp) (by simp))
          (pullback.fst f fT) (pullback.fst f.fromNormalization fT) f.toNormalization :=
        .of_right (t := .flip <| .of_hasPullback ..)
          (by simpa using (.flip <| .of_hasPullback ..)) (by cat_disch)
      exact .of_iso' H (.refl _) (asIso <| f.normalizationPullback fT) (.refl _) (.refl _)
        (by cat_disch) (by simp) (by simp [fTn]) (by simp)
    · simp [← cancel_mono U'.ι, fTnU, fTn]
  exact MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
    (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) this
    ⟨⟨‹_›, inferInstance⟩, inferInstance⟩ ‹_›

/--
**Zariski's main theorem**

Recall that any qcqs morphism `f : X ⟶ Y` factors through the relative normalization via
`f.toNormalization : X ⟶ f.normalization` (a dominant morphism) and
`f.fromNormalization : f.normalization ⟶ Y` (an integral morphism).

Let `f : X ⟶ Y` be separated and of finite type.

then there exists `U : f.normalization.Opens`, such that
1. `f.toNormalization ∣_ U` is an isomorphism
2. `f.toNormalization ⁻¹ᵁ U` is the quasi-finite locus of `f`
-/
@[stacks 03GW]
lemma Scheme.Hom.exists_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    ∃ U : f.normalization.Opens, IsIso (f.toNormalization ∣_ U) ∧
      (f.toNormalization ⁻¹ᵁ U).1 = { x | f.QuasiFiniteAt x } := by
  choose V hxV hV using fun x : { x // f.QuasiFiniteAt x } ↦
    f.exists_mem_and_isIso_morphismRestrict_toNormalization x x.2
  let 𝒰 := Opens.iSupOpenCover V
  have : IsIso (f.toNormalization ∣_ ⨆ x, V x) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
    refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
    have : Opens.ι _ ''ᵁ (𝒰.f x).opensRange = V x := by
      simp only [Opens.iSupOpenCover, 𝒰, ← opensRange_comp, homOfLE_ι, Opens.opensRange_ι]
    convert hV x
  refine ⟨⨆ x : { x | f.QuasiFiniteAt x }, V x, this, ?_⟩
  ext x
  suffices (∃ i : { x | f.QuasiFiniteAt x }, toNormalization f x ∈ V i) ↔ f.QuasiFiniteAt x by
    simpa
  refine ⟨?_, fun h ↦ ⟨⟨x, h⟩, hxV _⟩⟩
  rintro ⟨y, hxVy⟩
  obtain ⟨U, r, hU, hr, hxV, hrV⟩ :
      ∃ (U : Y.Opens) (r : Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U)),
      IsAffineOpen U ∧ IsAffineOpen (f.toNormalization ⁻¹ᵁ f.normalization.basicOpen r) ∧
      x ∈ f.toNormalization ⁻¹ᵁ f.normalization.basicOpen r ∧ Scheme.basicOpen _ r ≤ V y := by
    obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWV : W ≤ _⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hxVy (f.toNormalization ⁻¹ᵁ V y).isOpen
    have : IsAffine W := hW
    let V' := (X.homOfLE hWV ≫ f.toNormalization ∣_ V y ≫ (V y).ι).opensRange
    have hV' : IsAffineOpen V' := isAffineOpen_opensRange _
    have hV'V : V' ≤ V y := by
      simp_rw [V', ← Category.assoc, opensRange_comp]
      exact (image_le_opensRange _ _).trans (by simp)
    have hV'W : f.toNormalization ⁻¹ᵁ V' = W := by
      have : (f.toNormalization ⁻¹ᵁ V y).ι ⁻¹ᵁ f.toNormalization ⁻¹ᵁ V' =
          (f.toNormalization ⁻¹ᵁ V y).ι ⁻¹ᵁ W := by
        rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι]
        simp only [V', opensRange_comp, Scheme.Hom.preimage_image_eq, opensRange_homOfLE]
      simpa only [image_preimage_eq_opensRange_inf, Opens.opensRange_ι, ← preimage_inf,
        inf_eq_right.mpr, hV'V, hWV] using congr((f.toNormalization ⁻¹ᵁ V y).ι ''ᵁ $this)
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨f₁, f₂, e, hxf⟩ := exists_basicOpen_le_affine_inter (hU.preimage f.fromNormalization)
      hV' (f.toNormalization x) ⟨by simpa [← Scheme.Hom.comp_apply], hV'W.ge hxW⟩
    refine ⟨U, f₁, hU, ?_, hxf, (e.trans_le (f.normalization.basicOpen_le _)).trans hV'V⟩
    rw [e, preimage_basicOpen]
    exact IsAffineOpen.basicOpen (hV'W ▸ hW) _
  let W := f.toNormalization ⁻¹ᵁ f.normalization.basicOpen r
  have H : W ≤ f ⁻¹ᵁ U := by
    unfold W
    grw [Scheme.basicOpen_le, ← Scheme.Hom.comp_preimage, f.toNormalization_fromNormalization]
  have H' : f.fromNormalization.appLE _ _ ((normalization f).basicOpen_le _) ≫
    f.toNormalization.app _ = f.appLE U W H := by
    simp only [app_eq_appLE]
    exact (appLE_comp_appLE _ _ _ _ _ _ _).trans (by simp [W])
  have : IsIso ((toNormalization f).app ((normalization f).basicOpen r)) := by
    have H : (f.toNormalization ∣_ V y) ⁻¹ᵁ (V y).ι ⁻¹ᵁ (normalization f).basicOpen r =
        (Scheme.homOfLE _ (f.toNormalization.preimage_mono hrV)).opensRange := by
      apply Scheme.Hom.image_injective (f.toNormalization ∣_ V y)
      simp only [opensRange_homOfLE, image_preimage_eq_opensRange_inf]
      rw [← Scheme.Hom.comp_preimage, ← morphismRestrict_ι, Scheme.Hom.comp_preimage,
        image_preimage_eq_opensRange_inf]
    have := (inferInstance : IsIso ((toNormalization f ∣_ V y).app
      (Scheme.homOfLE _ hrV).opensRange))
    simp only [Opens.toScheme_presheaf_obj, app_eq_appLE, morphismRestrict_appLE] at this ⊢
    convert this <;>
      simp [Scheme.Hom.image_preimage_eq_opensRange_inf, -Scheme.preimage_basicOpen,
        f.toNormalization.preimage_mono, hrV, H]
  have : (f.appLE U W H).hom.QuasiFinite := by
    have : (f.appLE U W H).hom.FiniteType := f.finiteType_appLE hU hr H
    rw [← H', CommRingCat.hom_comp, RingHom.finiteType_respectsIso.cancel_right_isIso] at this
    rw [← H', CommRingCat.hom_comp, RingHom.QuasiFinite.respectsIso.cancel_right_isIso]
    exact .of_isIntegral_of_finiteType (IsIntegralHom.isIntegral_app f.fromNormalization _ hU)
      ⟨r, (hU.preimage f.fromNormalization).isLocalization_basicOpen _⟩ this
  have hxU : f x ∈ U := by
    convert show _ ∈ U from (normalization f).basicOpen_le _ hxV
    rw [← Scheme.Hom.comp_apply, f.toNormalization_fromNormalization]
  refine .of_comp (g := (Y.presheaf.germ U _ hxU).hom) ?_
  rw [← CommRingCat.hom_comp, f.germ_stalkMap, ← X.presheaf.germ_res (homOfLE H) _ hxV,
    app_eq_appLE, appLE_map_assoc, CommRingCat.hom_comp]
  refine .comp ?_ this
  have := hr.isLocalization_stalk ⟨x, hxV⟩
  let := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  rw [← RingHom.algebraMap_toAlgebra (X.presheaf.germ _ _ _).hom, @RingHom.quasiFinite_algebraMap]
  exact .of_isLocalization (hr.primeIdealOf ⟨x, hxV⟩).asIdeal.primeCompl

lemma Scheme.Hom.isOpen_quasiFiniteAt [LocallyOfFiniteType f] :
    IsOpen { x | f.QuasiFiniteAt x } := by
  wlog H : IsAffineHom f
  · rw [isOpen_iff_forall_mem_open]
    intro x hx
    obtain ⟨_, ⟨U : Y.Opens, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f x)) isOpen_univ
    obtain ⟨_, ⟨V : X.Opens, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      hxU (f ⁻¹ᵁ U).2
    have inst : IsAffineHom (f.resLE U V hVU) :=
      have : IsAffine _ := hU
      have : IsAffine _ := hV
      isAffineHom_of_isAffine _
    refine ⟨_, ?_, V.2.isOpenEmbedding_subtypeVal.isOpenMap _ (this (f.resLE U V hVU) inst), ?_⟩
    · rintro _ ⟨x : V, hx : (f.resLE U V hVU).QuasiFiniteAt _, rfl⟩
      rwa [← quasiFiniteAt_comp_iff (g := U.ι), resLE_comp_ι,
        quasiFiniteAt_comp_iff_of_isOpenImmersion] at hx
    · refine ⟨⟨x, hxV⟩, show (f.resLE _ _ _).QuasiFiniteAt _ from ?_, rfl⟩
      rwa [← quasiFiniteAt_comp_iff (g := U.ι), resLE_comp_ι,
        quasiFiniteAt_comp_iff_of_isOpenImmersion]
  obtain ⟨U, hU, e⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  exact e ▸ (f.toNormalization ⁻¹ᵁ U).2

/-- The set of quasi-finite points of a morphism `f : X ⟶ Y` as an `X.Opens`. -/
def Scheme.Hom.quasiFiniteLocus [LocallyOfFiniteType f] : X.Opens :=
  ⟨{ x | f.QuasiFiniteAt x }, f.isOpen_quasiFiniteAt⟩

variable {f} in
@[simp]
lemma Scheme.Hom.mem_quasiFiniteLocus [LocallyOfFiniteType f]
    {x : X} : x ∈ f.quasiFiniteLocus ↔ f.QuasiFiniteAt x := .rfl

instance [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion (f.quasiFiniteLocus.ι ≫ f.toNormalization) := by
  obtain ⟨U, hU, e⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  convert (inferInstance : IsOpenImmersion ((X.isoOfEq (U := f.quasiFiniteLocus)
    (SetLike.coe_injective e.symm)).hom ≫ f.toNormalization ∣_ U ≫ U.ι)) using 1
  simp

lemma Scheme.Hom.quasiFiniteLocus_eq_top [LocallyQuasiFinite f] [LocallyOfFiniteType f] :
    f.quasiFiniteLocus = ⊤ :=
  top_le_iff.mp fun x _ ↦ f.quasiFiniteAt x

lemma Scheme.Hom.quasiFiniteLocus_comp {Z : Scheme} [IsOpenImmersion f]
    (g : Y ⟶ Z) [LocallyOfFiniteType g] :
    (f ≫ g).quasiFiniteLocus = f ⁻¹ᵁ g.quasiFiniteLocus := by
  ext
  simp [quasiFiniteAt_comp_iff_of_isOpenImmersion]

lemma Scheme.Hom.quasiFiniteLocus_eq_top_iff [LocallyOfFiniteType f] :
    f.quasiFiniteLocus = ⊤ ↔ LocallyQuasiFinite f := by
  refine ⟨fun H ↦ locallyQuasiFinite_iff_isDiscrete_preimage_singleton.mpr fun x ↦ ?_,
    fun _ ↦ f.quasiFiniteLocus_eq_top⟩
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨a, rfl⟩
  rw [← (f.fiberHomeo _).symm.isOpen_image, Set.image_singleton]
  exact (H.ge (Set.mem_univ a)).isClopen_singleton_asFiber.isOpen

instance [LocallyOfFiniteType f] :
    LocallyQuasiFinite (f.quasiFiniteLocus.ι ≫ f) := by
  rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff, Scheme.Hom.quasiFiniteLocus_comp,
    Scheme.Opens.ι_preimage_self]

instance [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion f.toNormalization := by
  convert (inferInstance : IsOpenImmersion (X.topIso.inv ≫ (X.isoOfEq
    f.quasiFiniteLocus_eq_top).inv ≫ f.quasiFiniteLocus.ι ≫ f.toNormalization)) using 1
  simp

-- In particular it is surjective (by infer_instance), since it is a priori dominant.
instance [QuasiSeparated f] [UniversallyClosed f] : UniversallyClosed f.toNormalization :=
  have : UniversallyClosed (f.toNormalization ≫ f.fromNormalization) := by simpa
  .of_comp_of_isSeparated _ f.fromNormalization

lemma IsFinite.of_isProper_of_locallyQuasiFinite
    [IsProper f] [LocallyQuasiFinite f] : IsFinite f := by
  have : IsIso f.toNormalization :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  refine (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨?_, inferInstance⟩
  rw [← f.toNormalization_fromNormalization]
  infer_instance

@[stacks 02LS "(1) <=> (3)"]
lemma IsFinite.iff_isProper_and_locallyQuasiFinite :
    IsFinite f ↔ IsProper f ∧ LocallyQuasiFinite f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun ⟨_, _⟩ ↦ .of_isProper_of_locallyQuasiFinite f⟩

lemma IsFinite.eq_proper_inf_locallyQuasiFinite :
    @IsFinite = (@IsProper ⊓ @LocallyQuasiFinite : MorphismProperty Scheme) := by
  ext
  exact IsFinite.iff_isProper_and_locallyQuasiFinite ..

@[stacks 04XV "(1) <=> (2)"]
lemma IsClosedImmersion.iff_isProper_and_mono :
    IsClosedImmersion f ↔ IsProper f ∧ Mono f := by
  have (_ : Mono f) (_ : IsProper f) : LocallyQuasiFinite f := inferInstance
  rw [IsClosedImmersion.iff_isFinite_and_mono, IsFinite.iff_isProper_and_locallyQuasiFinite]
  aesop

lemma IsClosedImmersion.eq_proper_inf_monomorphisms :
    @IsClosedImmersion = ↑@IsProper ⊓ MorphismProperty.monomorphisms Scheme := by
  ext
  exact IsClosedImmersion.iff_isProper_and_mono ..

@[stacks 02UP]
lemma exists_isFinite_morphismRestrict_of_finite_preimage_singleton
    [IsProper f] (y : Y) (hx : (f ⁻¹' {y}).Finite) :
    ∃ V : Y.Opens, y ∈ V ∧ IsFinite (f ∣_ V) := by
  let V : Y.Opens := ⟨_, (f.isClosedMap _ f.quasiFiniteLocus.isOpen.isClosed_compl).isOpen_compl⟩
  refine ⟨V, ?_, ?_⟩
  · suffices ∀ x, f x = y → f.QuasiFiniteAt x by simpa [V, not_imp_not]
    rintro x rfl
    have : Finite (f.fiber (f x)) := (f.fiberHomeo (f x)).finite_iff.mpr ‹_›
    exact Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mpr (isOpen_discrete _)
  · suffices LocallyQuasiFinite (f ∣_ V) from .of_isProper_of_locallyQuasiFinite _
    rw [← Scheme.Hom.quasiFiniteLocus_eq_top_iff]
    ext x
    have : f.QuasiFiniteAt ((f ⁻¹ᵁ V).ι x) := by by_contra H; exact x.2 ⟨_, H, by simp⟩
    rw [← Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion, ← morphismRestrict_ι,
      Scheme.Hom.quasiFiniteAt_comp_iff] at this
    simpa

@[stacks 0AH8]
lemma exists_finite_imageι_comp_morphismRestrict_of_finite_image_preimage
    {X Y S : Scheme} (f : X ⟶ Y) (g : Y ⟶ S) (s : S)
    (H : (f '' ((f ≫ g) ⁻¹' {s})).Finite)
    [IsProper (f ≫ g)] [IsSeparated g] [LocallyOfFiniteType g] :
    ∃ U : S.Opens, s ∈ U ∧ IsFinite ((f.imageι ≫ g) ∣_ U) := by
  have : IsProper f := .of_comp f g
  have : IsProper (f.imageι ≫ g) := by
    suffices UniversallyClosed (f.imageι ≫ g) from ⟨⟩
    have : UniversallyClosed (f.toImage ≫ f.imageι ≫ g) := by
      rw [Scheme.Hom.toImage_imageι_assoc]; infer_instance
    refine .of_comp_surjective f.toImage _
  refine exists_isFinite_morphismRestrict_of_finite_preimage_singleton _ _ ?_
  refine .of_finite_image (f := f.imageι) (H.subset ?_) f.imageι.isClosedEmbedding.injective.injOn
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x, rfl⟩ := f.toImage.surjective x
  refine ⟨x, ?_, by simp [← Scheme.Hom.comp_apply]⟩
  simpa [← Scheme.Hom.comp_apply, -Scheme.Hom.comp_base] using hx

end AlgebraicGeometry

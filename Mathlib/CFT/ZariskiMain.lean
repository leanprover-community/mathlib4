import Mathlib
import Mathlib.CFT.EtaleLocalization
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.CFT.Normalization

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X Y S : Scheme.{u}} (f : X ⟶ Y)

@[simps]
def _root_.TopologicalSpace.Opens.frameHom {X : Type*} [TopologicalSpace X] :
    FrameHom (TopologicalSpace.Opens X) (Set X) where
  toFun := (·)
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' _ := by simp

lemma Scheme.Hom.exists_mem_and_isIso_morphismRestrict_toNormalization
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f]
    (x : X) (hx : x ∈ f.quasiFiniteLocus) :
    ∃ V, f.toNormalization x ∈ V ∧ IsIso (f.toNormalization ∣_ V) := by
  obtain ⟨T, fT, u, _, hu, V, W, v, hVW, _, hv₂⟩ := stacks02LN_easy _ rfl hx
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
      ← morphismRestrict_comp, ← isIso_comp_right_iff _ (IsOpenImmersion.opensRangeIso ι).inv]
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
    convert (inferInstanceAs (IsIso (Scheme.isoOfEq _ Heq).hom))
    rw [Iso.comp_inv_eq, ← Iso.inv_comp_eq, ← cancel_mono (Scheme.Opens.ι _)]
    have : V.ι ≫ (H.coconePointUniqueUpToIso (colimit.isColimit _)).hom = coprod.inl :=
      H.comp_coconePointUniqueUpToIso_hom _ ⟨.left⟩
    simp [e, IsOpenImmersion.opensRangeIso, Scheme.Hom.normalizationCoprodIso, reassoc_of% this, ι]
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
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := .isomorphisms _)
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
      (f.toNormalization ⁻¹ᵁ U).1 = f.quasiFiniteLocus := by
  choose V hxV hV using fun x : f.quasiFiniteLocus ↦
    f.exists_mem_and_isIso_morphismRestrict_toNormalization x x.2
  let 𝒰 := Opens.iSupOpenCover V
  have : IsIso (f.toNormalization ∣_ ⨆ x, V x) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
    refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
    have : Opens.ι _ ''ᵁ (𝒰.f x).opensRange = V x := by
      simp only [Opens.iSupOpenCover, 𝒰, ← opensRange_comp, homOfLE_ι, Opens.opensRange_ι]
    convert hV x
  refine ⟨⨆ x : f.quasiFiniteLocus, V x, this, ?_⟩
  ext x
  suffices (∃ i : quasiFiniteLocus f, toNormalization f x ∈ V i) ↔ x ∈ quasiFiniteLocus f by
    simpa
  refine ⟨?_, fun h ↦ ⟨⟨x, h⟩, hxV _⟩⟩
  rintro ⟨y, hxVy⟩
  obtain ⟨U, r, hU, hr, hxV, hrV⟩ : ∃ (U : Y.Opens) (r : Γ(_, f.fromNormalization ⁻¹ᵁ U)),
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
    have := (inferInstanceAs (IsIso ((toNormalization f ∣_ V y).app
      (Scheme.homOfLE _ hrV).opensRange)))
    simp only [Opens.toScheme_presheaf_obj, app_eq_appLE, morphismRestrict_appLE] at this ⊢
    convert this <;>
      simp [Scheme.Hom.image_preimage_eq_opensRange_inf, -Scheme.preimage_basicOpen,
        f.toNormalization.preimage_mono, hrV, H]
  have : (f.appLE U W H).hom.QuasiFinite := by
    have : (f.appLE U W H).hom.FiniteType :=
      LocallyOfFiniteType.finiteType_of_affine_subset ⟨_, hU⟩ ⟨_, hr⟩ _
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

lemma Scheme.Hom.isOpen_quasiFiniteLocus
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpen f.quasiFiniteLocus := by
  obtain ⟨U, hU, e⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  exact e ▸ (f.toNormalization ⁻¹ᵁ U).2

def Scheme.Hom.quasiFiniteOpen
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] : X.Opens :=
  ⟨_, f.isOpen_quasiFiniteLocus⟩

instance [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion (f.quasiFiniteOpen.ι ≫ f.toNormalization) := by
  obtain ⟨U, hU, e⟩ := Scheme.Hom.exists_isIso_morphismRestrict_toNormalization f
  convert inferInstanceAs (IsOpenImmersion ((X.isoOfEq (U := f.quasiFiniteOpen)
    (SetLike.coe_injective e.symm)).hom ≫ f.toNormalization ∣_ U ≫ U.ι)) using 1
  simp

lemma Scheme.Hom.quasiFiniteOpen_eq_top [LocallyQuasiFinite f]
    [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] : f.quasiFiniteOpen = ⊤ :=
  TopologicalSpace.Opens.ext f.quasiFiniteLocus_eq_univ

instance [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f] :
    IsOpenImmersion f.toNormalization := by
  convert inferInstanceAs (IsOpenImmersion (X.topIso.inv ≫ (X.isoOfEq
    f.quasiFiniteOpen_eq_top).inv ≫ f.quasiFiniteOpen.ι ≫ f.toNormalization)) using 1
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

lemma IsFinite.iff_isProper_and_locallyQuasiFinite :
    IsFinite f ↔ IsProper f ∧ LocallyQuasiFinite f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩,
    fun ⟨_, _⟩ ↦ .of_isProper_of_locallyQuasiFinite f⟩

end AlgebraicGeometry

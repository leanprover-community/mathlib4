
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.CFT.Flat
import Mathlib.CFT.IntegralClosure
import Mathlib.CFT.Smooth

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {X S Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [QuasiCompact f] [QuasiSeparated f]

lemma isIso_morphismRestrict_iff_isIso_app
    (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso (f ∣_ U) ↔ IsIso (f.app U) := by
  have : IsAffine U := hU
  refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)).trans <|
    (and_iff_right (hU.preimage f)).trans ?_
  rw [Scheme.Hom.app_eq_appLE]
  simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top]
  congr! <;> simp [Scheme.Opens.toScheme_presheaf_obj]

lemma isIso_pullbackSnd_opensι_iff_isIso_app
    (f : X ⟶ Y) [IsAffineHom f] {U : Y.Opens} (hU : IsAffineOpen U) :
    IsIso (pullback.snd f U.ι) ↔ IsIso (f.app U) := by
  have : IsAffine U := hU
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict, isIso_comp_left_iff,
    isIso_morphismRestrict_iff_isIso_app f hU]

lemma IsZariskiLocalAtTarget.of_forall_exists_isOpen {P : MorphismProperty Scheme}
    [IsZariskiLocalAtTarget P] {X Y : Scheme} {f : X ⟶ Y}
    (H : ∀ x, ∃ U : Y.Opens, x ∈ U ∧ P (f ∣_ U)) : P f := by
  choose U hxU hU using H
  refine IsZariskiLocalAtTarget.of_iSup_eq_top U (top_le_iff.mp fun x _ ↦ ?_) hU
  simpa using ⟨x, hxU x⟩

lemma IsIso_of_isAffineHom_of_forall_isAffineOpen {X S Y : Scheme.{u}} (fY : Y ⟶ S)
    [IsAffineHom fY] (f : X ⟶ Y) [IsAffineHom f]
    (H : ∀ U : S.Opens, IsAffineOpen U → IsIso (f.app (fY ⁻¹ᵁ U))) : IsIso f := by
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) (Y.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top S) fY.base.hom))).mpr fun (U : S.affineOpens) ↦ ?_
  have : IsAffine (fY ⁻¹ᵁ ↑U) := U.2.preimage fY
  refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms _)
    (f := pullback.snd f (fY ⁻¹ᵁ U).ι)).mpr ⟨isAffine_of_isAffineHom (pullback.snd _ _), ?_⟩
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict, Scheme.Hom.comp_appTop]
  simp_rw [Scheme.Hom.app_eq_appLE] at H
  simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top, isIso_comp_right_iff]
  suffices ∀ V₁ V₂ (h₁ : V₁ = fY ⁻¹ᵁ ↑U) (h₂ : V₂ = f ⁻¹ᵁ fY ⁻¹ᵁ ↑U),
      IsIso (f.appLE V₁ V₂ (by simp_all)) from this _ _ (by simp) (by simp)
  exact fun _ _ e₁ e₂ ↦ by subst e₁ e₂; exact H U.1 U.2

noncomputable
def Scheme.Hom.normalizationPullback :
    (pullback.snd f g).normalization ⟶ pullback f.fromNormalization g :=
  (pullback.snd f g).normalizationDesc (pullback.map _ _ _ _ f.toNormalization
    (𝟙 _) (𝟙 _) (by simp) (by simp)) (pullback.snd _ _) (by simp)
  deriving IsIntegralHom

@[reassoc (attr := simp)]
lemma Scheme.Hom.normalizationPullback_snd :
    f.normalizationPullback g ≫ pullback.snd _ _ = (pullback.snd f g).fromNormalization :=
  (pullback.snd f g).normalizationDesc_comp ..

@[reassoc (attr := simp)]
lemma Scheme.Hom.toNormalization_normalizationPullback_fst :
    (pullback.snd f g).toNormalization ≫ f.normalizationPullback g ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ f.toNormalization := by
  simp [normalizationPullback]

noncomputable
def Scheme.Hom.normalizationObjIso (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    Γ(f.normalization, f.fromNormalization ⁻¹ᵁ U) ≅
      .of (integralClosure Γ(Y, U) Γ(X, f ⁻¹ᵁ U)) :=
  f.normalization.presheaf.mapIso (eqToIso
    (by simpa using (f.fromNormalization_preimage ⟨U, hU⟩).symm)).op ≪≫
  (f.normalizationOpenCover.f ⟨U, hU⟩).appIso ⊤ ≪≫ Scheme.ΓSpecIso _

lemma Scheme.Hom.fromNormalization_app (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    f.fromNormalization.app U = CommRingCat.ofHom (algebraMap _ _) ≫
      (f.normalizationObjIso hU).inv := by
  letI := (f.app U).hom.toAlgebra
  have : IsIso (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)) :=
    Scheme.Hom.isIso_app _ _ (by simp [← fromNormalization_preimage])
  have H : ⊤ = ((normalizationOpenCover f).f ⟨U, hU⟩ ≫ fromNormalization f) ⁻¹ᵁ U := by
    rw [f.ι_fromNormalization]; simp
  rw [← cancel_mono (((normalizationOpenCover f).f ⟨U, hU⟩).app (f.fromNormalization ⁻¹ᵁ U)),
    ← Scheme.Hom.comp_app, Scheme.Hom.congr_app (f.ι_fromNormalization ⟨U, hU⟩) U,
    ← cancel_mono (((normalizationOpenCover f).X ⟨U, hU⟩).presheaf.map (eqToHom H).op)]
  dsimp [normalizationObjIso]
  rw [IsAffineOpen.fromSpec_app_self]
  simp only [app_eq_appLE, Category.assoc, map_appLE, appLE_map, appIso_inv_appLE]
  simp [Scheme.Hom.appLE, ← ΓSpecIso_inv_naturality]
  rfl

lemma Scheme.Hom.normalizationObjIso_hom_val (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    {U : Y.Opens} (hU : IsAffineOpen U) :
    letI := (f.app U).hom.toAlgebra
    (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom (Subalgebra.val _).toRingHom =
    f.toNormalization.appLE _ _ (by simp [← Scheme.Hom.comp_preimage]) := by
  dsimp [Scheme.Hom.normalizationObjIso]
  rw [Category.assoc, Category.assoc, ← IsIso.eq_inv_comp, ← Functor.map_inv, map_appLE]
  have H : toNormalization f ⁻¹ᵁ (normalizationOpenCover f).f ⟨U, hU⟩ ''ᵁ ⊤ = f ⁻¹ᵁ U := by
    simp [← fromNormalization_preimage, ← Scheme.Hom.comp_preimage]
  have : IsIso ((f ⁻¹ᵁ U).ι.app
      (toNormalization f ⁻¹ᵁ (normalizationOpenCover f).f ⟨U, hU⟩ ''ᵁ ⊤)) :=
    isIso_app _ _ (by rw [H]; simp)
  rw [← cancel_mono (X.presheaf.map (eqToHom H).op), ← cancel_mono ((f ⁻¹ᵁ U).ι.app _)]
  simp only [appLE_map, app_eq_appLE, appLE_comp_appLE]
  rw [Opens.ι_appLE, appLE, congr_app (f.ι_toNormalization ⟨U, hU⟩)]
  dsimp [Opens.toScheme_presheaf_obj]
  simp only [Category.assoc, ← Functor.map_comp, ← Iso.eq_inv_comp, appIso_inv_app_assoc,
    naturality_assoc, TopologicalSpace.Opens.map_top, Opens.toSpecΓ_appTop, Opens.topIso_inv,
    Quiver.Hom.unop_op, Opens.toScheme_presheaf_map]
  rw [ΓSpecIso_naturality_assoc]
  exact ((ΓSpecIso ((normalizationDiagram f).obj _)).inv_hom_id_assoc _).symm

open TensorProduct in
set_option maxHeartbeats 0 in
instance [Smooth g] : IsIso (f.normalizationPullback g) := by
  apply IsZariskiLocalAtTarget.of_forall_exists_isOpen (P := .isomorphisms _) fun x ↦ ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ ((pullback.snd _ g ≫ g) x)) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ g ⁻¹ᵁ U⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (a := pullback.snd _ g x) hxU (g ⁻¹ᵁ U).2
  let W := pullback.snd (Scheme.Hom.fromNormalization f) g ⁻¹ᵁ V
  refine ⟨W, hxV, (isIso_morphismRestrict_iff_isIso_app _ (U := W) (hV.preimage _)).mpr ?_⟩
  have := isIso_pushoutDesc_appLE_appLE_of_isCompact_of_isQuasiSeparated_of_flat
    (.of_hasPullback f.fromNormalization g) hU hV hVU le_rfl (UY := W)
    (by simp_rw [W, ← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU])
    (hU.preimage f.fromNormalization).isCompact (hU.preimage f.fromNormalization).isQuasiSeparated
  rw [← @isIso_comp_left_iff _ _ _ _ _ _ _ this,
    ← isIso_comp_left_iff (pushout.congrHom f.fromNormalization.app_eq_appLE rfl).hom]
  have : (g.appLE U V hVU).hom.Smooth := Smooth.smooth_of_affine_subset ⟨U, hU⟩ ⟨V, hV⟩ _
  algebraize [(f.app U).hom, (g.appLE U V hVU).hom, ((pullback.snd f g).app V).hom]
  have := isIso_pushoutDesc_appLE_appLE_of_isCompact_of_isQuasiSeparated_of_flat
    (.of_hasPullback f g) hU hV hVU le_rfl (UY := pullback.snd f g ⁻¹ᵁ V)
    (by simp_rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage,
      ← Scheme.Hom.preimage_inf, inf_eq_right.mpr hVU]) (f.isCompact_preimage hU.isCompact)
    (f.isQuasiSeparated_preimage hU.isQuasiSeparated)
  let e₀ := (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout ≪≫
    (pushout.congrHom f.app_eq_appLE rfl ≪≫ @asIso _ _ _ _ _ this:)
  let e : Γ(Y, V) ⊗[Γ(S, U)] Γ(X, f ⁻¹ᵁ U) ≃ₐ[Γ(Y, V)] Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    { toRingEquiv := e₀.commRingCatIsoToRingEquiv,
      commutes' r := by
        change (CommRingCat.ofHom Algebra.TensorProduct.includeLeftRingHom ≫ e₀.hom) r =
          (pullback.snd f g).app V r
        congr 2
        simp [e₀, pushout.inr_desc_assoc, Scheme.Hom.app_eq_appLE] }
  let ψ : Γ(Y, V) ⊗[Γ(S, U)] integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U) →ₐ[Γ(Y, V)]
      integralClosure Γ(Y, V) Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V) :=
    e.mapIntegralClosure.toAlgHom.comp (TensorProduct.toIntegralClosure _ _ _)
  have hψ : Function.Bijective ψ := e.mapIntegralClosure.bijective.comp
    TensorProduct.toIntegralClosure_bijective_of_smooth
  let φ : pushout (f.fromNormalization.app U) (g.appLE U V hVU) ⟶
      Γ((pullback.snd f g).normalization, f.normalizationPullback g ⁻¹ᵁ W) :=
    pushout.map _ _ (CommRingCat.ofHom (algebraMap Γ(S, U) (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U))))
      (g.appLE U V hVU) (f.normalizationObjIso hU).hom (𝟙 _) (𝟙 _)
      (by simp [Scheme.Hom.fromNormalization_app _ hU]) (by simp) ≫
    (CommRingCat.isPushout_tensorProduct ..).flip.isoPushout.inv ≫
    (RingEquiv.ofBijective ψ.toRingHom hψ).toCommRingCatIso.hom ≫
    ((pullback.snd f g).normalizationObjIso hV).inv ≫
    (pullback.snd f g).normalization.presheaf.map (eqToHom
      (by simp only [W, ← Scheme.Hom.comp_preimage, Scheme.Hom.normalizationPullback_snd])).op
  convert show IsIso φ by dsimp only [φ]; infer_instance using 1
  ext1
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_left, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE, eqToHom_op,
      Category.assoc, IsPushout.inl_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, IsIso.Iso.inv_inv,
      Category.assoc]
    have : Mono (CommRingCat.ofHom (integralClosure Γ(Y, V)
        Γ(pullback f g, pullback.snd f g ⁻¹ᵁ V)).val.toRingHom) :=
      ConcreteCategory.mono_of_injective _ Subtype.val_injective
    rw [← cancel_mono (CommRingCat.ofHom (Subalgebra.val _).toRingHom)]
    simp only [Category.assoc, Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.toNormalization_normalizationPullback_fst, ← CommRingCat.ofHom_comp]
    have H : pullback.snd f g ⁻¹ᵁ V ≤ pullback.fst f g ⁻¹ᵁ f ⁻¹ᵁ U := by
      rw [← Scheme.Hom.comp_preimage, pullback.condition, Scheme.Hom.comp_preimage]
      exact Scheme.Hom.preimage_mono _ hVU
    trans (f.normalizationObjIso hU).hom ≫ CommRingCat.ofHom
        (integralClosure Γ(S, U) Γ(X, f ⁻¹ᵁ U)).val.toRingHom ≫ (pullback.fst f g).appLE _ _ H
    · rw [reassoc_of% Scheme.Hom.normalizationObjIso_hom_val, Scheme.Hom.appLE_comp_appLE]
    · congr 1
      ext x
      change (pullback.fst f g).appLE _ _ H x = _
      trans (CommRingCat.ofHom Algebra.TensorProduct.includeRight.toRingHom ≫ e₀.hom) x
      · congr 2; simp [e₀, pushout.inl_desc_assoc]
      · simp [ψ, toIntegralClosure, e]; rfl
  · dsimp [φ]
    simp only [Scheme.Hom.app_eq_appLE, colimit.ι_desc_assoc, span_right, PushoutCocone.mk_pt,
      PushoutCocone.mk_ι_app, Category.id_comp, Scheme.Hom.appLE_comp_appLE,
      Scheme.Hom.normalizationPullback_snd, eqToHom_op, IsPushout.inr_isoPushout_inv_assoc]
    simp_rw [← Category.assoc, ← IsIso.comp_inv_eq]
    simp only [← Functor.map_inv, inv_eqToHom, Scheme.Hom.appLE_map, ← Scheme.Hom.app_eq_appLE,
      Scheme.Hom.fromNormalization_app _ hV, IsIso.Iso.inv_inv, Category.assoc, Iso.inv_hom_id,
      Category.comp_id]
    exact congr(CommRingCat.ofHom $(ψ.comp_algebraMap.symm))

end AlgebraicGeometry

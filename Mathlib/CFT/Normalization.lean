
import Mathlib.AlgebraicGeometry.Normalization
import Mathlib.CFT.Flat
import Mathlib.CFT.IntegralClosure
import Mathlib.CFT.Smooth

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

section

variable {X Y X' Y' T : Scheme.{u}} (f : X ⟶ Y) (f₁ : X ⟶ T) (f₂ : T ⟶ Y)
  [QuasiCompact f] [QuasiSeparated f] [IsIntegralHom f₂]

noncomputable
def Scheme.Hom.normalizationDesc (H : f = f₁ ≫ f₂) : f.normalization ⟶ T := by
  refine colimit.desc _
    { pt := _
      ι.app U := Spec.map (CommRingCat.ofHom ((f₁.appLE _ _ (by simp [H])).hom.codRestrict _
        fun x ↦ ?_)) ≫ (U.2.preimage f₂).fromSpec,
      ι.naturality := ?_ }
  · change (f.app U.1).hom.IsIntegralElem _
    convert (f₂.isIntegral_app U.1 U.2 x).map (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])).hom
    simp only [← CommRingCat.hom_comp, Hom.app_eq_appLE, Hom.appLE_comp_appLE, ← H]
  · intros U V i
    dsimp
    rw [Category.comp_id, ← Spec.map_comp_assoc, ← (V.2.preimage f₂).map_fromSpec (U.2.preimage f₂)
      (homOfLE (f₂.preimage_mono (Scheme.AffineZariskiSite.toOpens_mono i.le))).op,
      ← Spec.map_comp_assoc]
    congr 2
    ext i
    apply Subtype.ext
    dsimp [normalizationDiagram]
    simp only [← CommRingCat.comp_apply, appLE_map, map_appLE]

@[reassoc (attr := simp)]
lemma Scheme.Hom.toNormalization_normalizationDesc (H : f = f₁ ≫ f₂) :
    f.toNormalization ≫ f.normalizationDesc f₁ f₂ H = f₁ := by
  refine Scheme.Cover.hom_ext (X.openCoverOfIsOpenCover _
    (.comap (iSup_affineOpens_eq_top Y) f.base.hom)) _ _ fun U ↦ ?_
  letI := (f.app U.1).hom.toAlgebra
  refine (Scheme.Hom.ι_toNormalization_assoc ..).trans ?_
  dsimp [normalizationOpenCover, normalizationDesc]
  simp only [colimit.ι_desc, ← Spec.map_comp_assoc]
  change (f ⁻¹ᵁ U.1).toSpecΓ ≫ Spec.map (f₁.appLE (f₂ ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) (by simp [H])) ≫
    (U.2.preimage f₂).fromSpec = _
  simp
  rfl

@[reassoc (attr := simp)]
lemma Scheme.Hom.normalizationDesc_comp (H : f = f₁ ≫ f₂) :
    f.normalizationDesc f₁ f₂ H ≫ f₂ = f.fromNormalization := by
  refine colimit.hom_ext fun U ↦ ?_
  dsimp [normalizationDesc, fromNormalization]
  rw [colimit.ι_desc_assoc, colimit.ι_desc, Category.assoc,
    ← IsAffineOpen.SpecMap_appLE_fromSpec _ U.2 _ le_rfl, ← Spec.map_comp_assoc]
  congr 2
  ext i
  dsimp [normalizationDiagram, normalizationDiagramMap, RingHom.algebraMap_toAlgebra]
  rw [← CommRingCat.comp_apply, Hom.appLE_comp_appLE, app_eq_appLE]
  simp_rw [H]

instance (H : f = f₁ ≫ f₂) : IsIntegralHom (f.normalizationDesc f₁ f₂ H) := by
  have : IsIntegralHom (f.normalizationDesc f₁ f₂ H ≫ f₂) := by
    rw [f.normalizationDesc_comp]; infer_instance
  exact .of_comp _ f₂

/-- If `φ` is a monomorphism in `CommRingCat`, it is not true that `Spec φ` is an epimorphism.
But the range of `f g : Spec R ⟶ X` are contained in an common affine open `U`, one can still
cancel `Spec.map φ ≫ f = Spec.map φ ≫ g` to get `f = g`. -/
lemma eq_of_SpecMap_comp_eq_of_isAffineOpen {R S : CommRingCat} (φ : R ⟶ S)
    (hφ : Function.Injective φ)
    {f g : Spec R ⟶ X} (U : X.Opens) (hU : IsAffineOpen U) (hUf : f ⁻¹ᵁ U = ⊤) (hUg : g ⁻¹ᵁ U = ⊤)
    (H : Spec.map φ ≫ f = Spec.map φ ≫ g) : f = g := by
  have : Mono φ := ConcreteCategory.mono_of_injective _ hφ
  rw [← IsOpenImmersion.lift_fac U.ι f (by simpa [Set.range_subset_iff] using fun x hx ↦ hUf.ge hx),
    ← IsOpenImmersion.lift_fac U.ι g (by simpa [Set.range_subset_iff] using fun x hx ↦ hUg.ge hx)]
  congr 1
  rw [← cancel_mono hU.isoSpec.hom, ← Spec.homEquiv.injective.eq_iff,
    ← cancel_mono φ, ← Spec.map_injective.eq_iff]
  simp [← cancel_mono U.ι, H]

lemma Scheme.Hom.normalization_hom_ext (f₁ f₂ : f.normalization ⟶ T) (g : T ⟶ Y) [IsAffineHom g]
    (H₁ : f.toNormalization ≫ f₁ = f.toNormalization ≫ f₂)
    (hf₁ : f₁ ≫ g = f.fromNormalization) (hf₂ : f₂ ≫ g = f.fromNormalization) : f₁ = f₂ := by
  apply f.normalizationOpenCover.hom_ext _ _ fun U ↦ ?_
  let := (f.app U.1).hom.toAlgebra
  have : IsAffineHom f₁ := have : IsAffineHom (f₁ ≫ g) := hf₁ ▸ inferInstance; .of_comp _ g
  have : IsAffineHom f₂ := have : IsAffineHom (f₂ ≫ g) := hf₂ ▸ inferInstance; .of_comp _ g
  let f₀ := toNormalization f ≫ f₁
  have hf₀ : f₀ = toNormalization f ≫ f₂ := H₁
  refine eq_of_SpecMap_comp_eq_of_isAffineOpen
    (CommRingCat.ofHom (integralClosure Γ(Y, U.1) Γ(X, f ⁻¹ᵁ U.1)).val.toRingHom)
    Subtype.val_injective _ (U.2.preimage g) ?_ ?_ ?_
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₁, ι_fromNormalization]; simp
  · simp only [← Scheme.Hom.comp_preimage, Category.assoc, hf₂, ι_fromNormalization]; simp
  · have h₁ : f ⁻¹ᵁ U.1 ≤ f₀ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, f₀, Category.assoc,
        hf₁, toNormalization_fromNormalization]; rfl
    have h₁' : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂, toNormalization_fromNormalization]
    have h₂ : fromNormalization f ⁻¹ᵁ U.1 = f₁ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₁]
    have h₂' : fromNormalization f ⁻¹ᵁ U.1 = f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1 := by
      simp only [← Scheme.Hom.comp_preimage, hf₂]
    have h₃ : f ⁻¹ᵁ U.1 = toNormalization f ⁻¹ᵁ fromNormalization f ⁻¹ᵁ U.1 := by
      simp [← Scheme.Hom.comp_preimage]
    trans Spec.map (f₀.appLE _ _ h₁) ≫ (U.2.preimage g).fromSpec
    · simp only [AlgHom.toRingHom_eq_coe, comp_appLE, Spec.map_comp, Category.assoc, f₀,
        app_eq_appLE]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₁ ⁻¹ᵁ g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) h₁ =
        f.normalization.presheaf.map (eqToHom h₂).op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.1) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this, f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top]
    · simp only [AlgHom.toRingHom_eq_coe, hf₀, comp_appLE, Spec.map_comp, Category.assoc,
        app_eq_appLE]
      rw [IsAffineOpen.SpecMap_appLE_fromSpec _ _ ((U.2.preimage _).preimage _)]
      have : (toNormalization f).appLE (f₂ ⁻¹ᵁ g ⁻¹ᵁ U.1) (f ⁻¹ᵁ U.1) h₁'.le =
        f.normalization.presheaf.map (eqToHom h₂').op ≫
        (toNormalization f).app (f.fromNormalization ⁻¹ᵁ U.1) ≫
          X.presheaf.map (eqToHom h₃).op := by
        simp [app_eq_appLE]
      rw [this, f.toNormalization_app_preimage U]
      simp [appIso_hom', IsAffineOpen.SpecMap_appLE_fromSpec_assoc _ _ (isAffineOpen_top (Spec _)),
        IsAffineOpen.fromSpec_top]


end

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

noncomputable
def Scheme.coprodPresheafObjIso {X Y : Scheme.{u}} (U : (X ⨿ Y).Opens) :
    Γ(X ⨿ Y, U) ≅ Γ(X, coprod.inl (C := Scheme) ⁻¹ᵁ U) ⨯ Γ(Y, coprod.inr (C := Scheme) ⁻¹ᵁ U) :=
  letI ι₁ : X ⟶ X ⨿ Y := coprod.inl
  letI ι₂ : Y ⟶ X ⨿ Y := coprod.inr
  haveI h₁ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊔ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = U := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_sup_right, (isCompl_opensRange_inl_inr X Y).sup_eq_top, top_inf_eq]
  haveI h₂ : ι₁ ''ᵁ ι₁ ⁻¹ᵁ U ⊓ ι₂ ''ᵁ ι₂ ⁻¹ᵁ U = ⊥ := by
    simp_rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    rw [← inf_inf_distrib_right, (isCompl_opensRange_inl_inr X Y).inf_eq_bot, bot_inf_eq]
  (X ⨿ Y).presheaf.mapIso (eqToIso h₁).op ≪≫
    ((X ⨿ Y).sheaf.isProductOfDisjoint _ _ h₂).conePointUniqueUpToIso (limit.isLimit _) ≪≫
    prod.mapIso (ι₁.appIso _) (ι₂.appIso _)

lemma RingHom.IsIntegral.prod_iff {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S × T} : f.IsIntegral ↔
      ((RingHom.fst S T).comp f).IsIntegral ∧ ((RingHom.snd S T).comp f).IsIntegral := by
  refine ⟨fun H ↦ ⟨H.trans _ _ (.of_finite (.of_surjective _ Prod.fst_surjective)),
      H.trans _ _ (.of_finite (.of_surjective _ Prod.snd_surjective))⟩, fun ⟨h₁, h₂⟩ ↦ ?_⟩
  algebraize [(RingHom.fst S T).comp f, (RingHom.snd S T).comp f]
  exact algebraMap_isIntegral_iff.mpr inferInstance

instance {X Y X' Y' : Scheme.{u}}
    (f : X ⟶ X') (g : Y ⟶ Y') [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (coprod.map f g) := by
  refine IsZariskiLocalAtTarget.of_openCover (coprodOpenCover.{_, 0} _ _) ?_
  rintro (⟨⟨⟩⟩ | ⟨⟨⟩⟩)
  · let e : pullback (coprod.map f g) coprod.inl ≅ X :=
      IsOpenImmersion.isoOfRangeEq (pullback.fst _ _) coprod.inl (by
      rw [IsOpenImmersion.range_pullbackFst]
      apply subset_antisymm
      · rintro x ⟨y, hxy⟩
        obtain ⟨(x | x), rfl⟩ := (coprodMk _ _).surjective x
        · simp
        · simp only [coprodMk_inr, ← Scheme.Hom.comp_apply, coprod.inr_map] at hxy
          cases Set.disjoint_iff_forall_ne.mp (isCompl_range_inl_inr _ _).1 ⟨y, rfl⟩ ⟨_, rfl⟩ hxy
      · rintro _ ⟨x, rfl⟩
        exact ⟨f x, by simp [← Scheme.Hom.comp_apply, - Scheme.Hom.comp_base]⟩)
    change IsOpenImmersion (pullback.snd (coprod.map f g) coprod.inl)
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion e.inv]
    convert ‹IsOpenImmersion f›
    simp [e, ← cancel_mono (coprod.inl : X' ⟶ X' ⨿ Y'), ← pullback.condition]
  · let e : pullback (coprod.map f g) coprod.inr ≅ Y :=
      IsOpenImmersion.isoOfRangeEq (pullback.fst _ _) coprod.inr (by
      rw [IsOpenImmersion.range_pullbackFst]
      apply subset_antisymm
      · rintro x ⟨y, hxy⟩
        obtain ⟨(x | x), rfl⟩ := (coprodMk _ _).surjective x
        · simp only [coprodMk_inl, ← Scheme.Hom.comp_apply, coprod.inl_map] at hxy
          cases Set.disjoint_iff_forall_ne.mp
            (isCompl_range_inl_inr _ _).1 ⟨_, rfl⟩ ⟨_, rfl⟩ hxy.symm
        · simp
      · rintro _ ⟨x, rfl⟩
        exact ⟨g x, by simp [← Scheme.Hom.comp_apply, - Scheme.Hom.comp_base]⟩)
    change IsOpenImmersion (pullback.snd (coprod.map f g) coprod.inr)
    rw [← MorphismProperty.cancel_left_of_respectsIso @IsOpenImmersion e.inv]
    convert ‹IsOpenImmersion g›
    simp [e, ← cancel_mono (coprod.inr : Y' ⟶ X' ⨿ Y'), ← pullback.condition]

instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsAffineHom f] [IsAffineHom g] :
    IsAffineHom (coprod.desc f g) := by
  refine ⟨fun W hW ↦ ?_⟩
  have : IsAffine (f ⁻¹ᵁ W).toScheme := hW.preimage f
  have : IsAffine (g ⁻¹ᵁ W).toScheme := hW.preimage g
  let i : (f ⁻¹ᵁ W).toScheme ⨿ (g ⁻¹ᵁ W).toScheme ⟶ U ⨿ V := coprod.map (f ⁻¹ᵁ W).ι (g ⁻¹ᵁ W).ι
  convert isAffineOpen_opensRange i
  apply le_antisymm
  · intro x hx
    obtain ⟨(x | x), rfl⟩ := (coprodMk U V).surjective x
    · replace hx : f x ∈ W := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨coprodMk _ _ (.inl ⟨x, hx⟩), by simp [i, ← Scheme.Hom.comp_apply]⟩
    · replace hx : g x ∈ W := by simpa [← Scheme.Hom.comp_apply] using hx
      exact ⟨coprodMk _ _ (.inr ⟨x, hx⟩), by simp [i, ← Scheme.Hom.comp_apply]⟩
  · rintro _ ⟨x, rfl⟩
    obtain ⟨(⟨x, hx⟩ | ⟨x, hx⟩), rfl⟩ := (coprodMk _ _).surjective x
    · simpa [← Scheme.Hom.comp_apply, i] using hx
    · simpa [← Scheme.Hom.comp_apply, i] using hx

instance {U V X : Scheme.{u}} (f : U ⟶ X) (g : V ⟶ X) [IsIntegralHom f] [IsIntegralHom g] :
    IsIntegralHom (coprod.desc f g) := by
  refine ⟨fun W hW ↦ ?_⟩
  let e : Γ(U ⨿ V, coprod.desc f g ⁻¹ᵁ W) ≅ Γ(U, f ⁻¹ᵁ W) ⨯ Γ(V, g ⁻¹ᵁ W) :=
    Scheme.coprodPresheafObjIso _ ≪≫ prod.mapIso
      (U.presheaf.mapIso (eqToIso (by simp [← Scheme.Hom.comp_preimage])).op)
      (V.presheaf.mapIso (eqToIso (by simp [← Scheme.Hom.comp_preimage])).op)
  rw [← RingHom.isIntegral_respectsIso.cancel_right_isIso _ e.hom,
    ← CommRingCat.hom_comp, ← RingHom.isIntegral_respectsIso.cancel_right_isIso _
    ((CommRingCat.prodFanIsLimit _ _).conePointUniqueUpToIso (limit.isLimit _)).inv,
    ← CommRingCat.hom_comp]
  refine RingHom.IsIntegral.prod_iff.mpr ⟨?_, ?_⟩
  · have : (coprod.desc f g).app W ≫ e.hom ≫
        ((CommRingCat.prodFanIsLimit _ _).conePointUniqueUpToIso (limit.isLimit _)).inv ≫
        CommRingCat.ofHom (RingHom.fst _ _) = f.app W := by
      change (coprod.desc f g).app W ≫ e.hom ≫ prod.fst = _
      simp [e, Scheme.coprodPresheafObjIso, Scheme.Hom.appIso_hom',
        SheafedSpace.sheaf, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    convert f.isIntegral_app W hW
    exact congr(($this).1)
  · have : (coprod.desc f g).app W ≫ e.hom ≫
        ((CommRingCat.prodFanIsLimit _ _).conePointUniqueUpToIso (limit.isLimit _)).inv ≫
        CommRingCat.ofHom (RingHom.snd _ _) = g.app W := by
      change (coprod.desc f g).app W ≫ e.hom ≫ prod.snd = _
      simp [e, Scheme.coprodPresheafObjIso, Scheme.Hom.appIso_hom',
        SheafedSpace.sheaf, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    convert g.isIntegral_app W hW
    exact congr(($this).1)

noncomputable
def Scheme.Hom.normalizationCoprodIso {U V : Scheme} (iU : U ⟶ X) (iV : V ⟶ X) (f : X ⟶ Y)
    [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact iU] [QuasiSeparated iU] [QuasiCompact iV] [QuasiSeparated iV]
    (e : IsColimit (BinaryCofan.mk iU iV)) :
    (iU ≫ f).normalization ⨿ (iV ≫ f).normalization ≅ f.normalization where
  hom := coprod.desc
      ((iU ≫ f).normalizationDesc (iU ≫ f.toNormalization) f.fromNormalization (by simp))
      ((iV ≫ f).normalizationDesc (iV ≫ f.toNormalization) f.fromNormalization (by simp))
  inv := f.normalizationDesc ((e.coconePointUniqueUpToIso (colimit.isColimit _)).hom ≫
      coprod.map (iU ≫ f).toNormalization (iV ≫ f).toNormalization)
      (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) <| by
    simp only [← Iso.inv_comp_eq, Category.assoc]
    apply coprod.hom_ext <;> simp
  hom_inv_id := by
    ext
    · refine Scheme.Hom.normalization_hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iU ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inl :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.left⟩
      simp [reassoc_of% H]
    · refine Scheme.Hom.normalization_hom_ext _ _ _
        (coprod.desc (iU ≫ f).fromNormalization (iV ≫ f).fromNormalization) ?_ (by simp) (by simp)
      have H : iV ≫ (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).hom = coprod.inr :=
        e.comp_coconePointUniqueUpToIso_hom (colimit.isColimit (pair U V)) ⟨.right⟩
      simp [reassoc_of% H]
  inv_hom_id := by
    refine Scheme.Hom.normalization_hom_ext _ _ _ f.fromNormalization ?_ (by simp) (by simp)
    rw [← cancel_epi (e.coconePointUniqueUpToIso (colimit.isColimit (pair U V))).inv]
    apply coprod.hom_ext <;> simp

end AlgebraicGeometry

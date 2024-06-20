/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

/-!

# Affine morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is affine if the preimage of affine opens are affine.

-/

universe v u

open CategoryTheory TopologicalSpace Opposite

namespace AlgebraicGeometry

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- A morphism of schemes `X ⟶ Y` is affine if the preimages of affine open sets are affine. -/
@[mk_iff]
class IsAffineHom {X Y : Scheme} (f : X ⟶ Y) : Prop where
  isAffine_preimage : ∀ U : Opens Y, IsAffineOpen U → IsAffineOpen (f ⁻¹ᵁ U)

/-- The preimage of an affine open as an `Scheme.affine_opens`. -/
@[simps]
def affinePreimage {X Y : Scheme} (f : X ⟶ Y) [IsAffineHom f] (U : Y.affineOpens) :
    X.affineOpens :=
⟨f ⁻¹ᵁ U.1, IsAffineHom.isAffine_preimage _ U.prop⟩

instance (priority := 900) [IsIso f] : IsAffineHom f :=
⟨fun _ hU ↦ hU.map_isIso f⟩

instance (priority := 900) [IsAffineHom f] : QuasiCompact f :=
(quasiCompact_iff_forall_affine f).mpr (fun U hU ↦ (IsAffineHom.isAffine_preimage U hU).isCompact)

instance [IsAffineHom f] [IsAffineHom g] : IsAffineHom (f ≫ g) := by
  constructor
  intros U hU
  rw [Scheme.comp_val_base, Opens.map_comp_obj]
  apply IsAffineHom.isAffine_preimage
  apply IsAffineHom.isAffine_preimage
  exact hU

instance : MorphismProperty.IsMultiplicative @IsAffineHom where
  id_mem := inferInstance
  comp_mem _ _ _ _ := inferInstance

/-- The `AffineTargetMorphismProperty` corresponding to affine morphisms. -/
def IsAffineHom.affineProperty : AffineTargetMorphismProperty :=
fun X _ _ _  ↦ IsAffine X

@[simp] lemma IsAffineHom.affineProperty_toProperty :
  AffineTargetMorphismProperty.toProperty IsAffineHom.affineProperty f ↔
    IsAffine Y ∧ IsAffine X := by
  delta AffineTargetMorphismProperty.toProperty IsAffineHom.affineProperty; simp

lemma isAffineHom_iff_affineProperty :
    IsAffineHom f ↔ targetAffineLocally IsAffineHom.affineProperty f :=
(isAffineHom_iff f).trans ⟨fun H U ↦ H U U.prop, fun H U hU ↦ H ⟨U, hU⟩⟩

lemma isAffineHom_eq_affineProperty :
    @IsAffineHom = targetAffineLocally IsAffineHom.affineProperty := by
  ext; exact isAffineHom_iff_affineProperty _

instance {X : Scheme} (r : X.presheaf.obj (op ⊤)) :
    IsAffineHom (Scheme.ιOpens (X.basicOpen r)) := by
  constructor
  intros U hU
  fapply (Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion (Scheme.ιOpens _)).mp
  convert hU.basicOpenIsAffine (X.presheaf.map (homOfLE le_top).op r)
  rw [X.basicOpen_res]
  ext1
  refine Set.image_preimage_eq_inter_range.trans ?_
  erw [Subtype.range_coe]
  rfl

lemma isomorphisms_isLocalAtTarget :
    PropertyIsLocalAtTarget (MorphismProperty.isomorphisms _) := by
  constructor
  · exact MorphismProperty.RespectsIso.isomorphisms _
  · rintro X Y f U h
    have : IsIso f := h
    delta morphismRestrict MorphismProperty.isomorphisms
    infer_instance
  · intros X Y f 𝒰 h
    simp only [MorphismProperty.isomorphisms] at h
    have h := h -- why?
    rw [MorphismProperty.isomorphisms, isIso_iff_isOpenImmersion,
      IsOpenImmersion.openCover_iff 𝒰, TopCat.epi_iff_surjective]
    refine ⟨fun _ ↦ inferInstance, fun x ↦ ?_⟩
    obtain ⟨y, e⟩ := 𝒰.Covers x
    use (inv (Limits.pullback.snd (f := f) (g := 𝒰.map (𝒰.f x))) ≫ Limits.pullback.fst).1.base y
    rwa [← Scheme.comp_val_base_apply, Category.assoc, Limits.pullback.condition,
      IsIso.inv_hom_id_assoc]

lemma PrimeSpectrum.iSup_basicOpen_eq_top_iff {R : Type*} [CommRing R] {ι : Type*}
    {f : ι → R} : (⨆ i : ι, PrimeSpectrum.basicOpen (f i)) = ⊤ ↔ Ideal.span (Set.range f) = ⊤ := by
  rw [SetLike.ext'_iff, Opens.coe_iSup]
  simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Opens.coe_top, ← Set.compl_iInter,
    ← PrimeSpectrum.zeroLocus_iUnion]
  rw [← PrimeSpectrum.zeroLocus_empty_iff_eq_top, compl_involutive.eq_iff]
  simp only [Set.iUnion_singleton_eq_range,  Set.compl_univ, PrimeSpectrum.zeroLocus_span]

lemma PrimeSpectrum.iSup_basicOpen_eq_top_iff' {R : Type*} [CommRing R]
    {s : Set R} : (⨆ i ∈ s, PrimeSpectrum.basicOpen i) = ⊤ ↔ Ideal.span s = ⊤ := by
  conv_rhs => rw [← Subtype.range_val (s := s), ← iSup_basicOpen_eq_top_iff]
  simp

lemma isIso_of_isAffine_isIso {X Y : Scheme} [hX : IsAffine X] [hY : IsAffine Y] (f : X ⟶ Y)
    [hf : IsIso (f.1.c.app (op ⊤))] : IsIso f := by
  rw [← mem_Spec_essImage] at hX hY
  let f' : (⟨X, hX⟩ : AffineScheme) ⟶ ⟨Y, hY⟩ := f
  have : IsIso (AffineScheme.Γ.map f'.op) := hf
  have : AffineScheme.Γ.ReflectsIsomorphisms := reflectsIsomorphisms_of_full_and_faithful _
  have := isIso_of_reflects_iso f'.op AffineScheme.Γ
  have := isIso_of_op f'
  exact Functor.map_isIso AffineScheme.forgetToScheme f'

lemma ΓSpec.adjunction_unit_map_basicOpen (X : Scheme) (r : X.presheaf.obj (op ⊤)) :
    (ΓSpec.adjunction.unit.app X ⁻¹ᵁ (PrimeSpectrum.basicOpen r)) = X.basicOpen r := by
  rw [← basicOpen_eq_of_affine]
  erw [Scheme.preimage_basicOpen]
  congr
  rw [ΓSpec.adjunction_unit_app_app_top]
  erw [← comp_apply]
  simp

theorem ΓSpec.toOpen_unit_app_val_c_app {X : Scheme} (U) :
    StructureSheaf.toOpen _ _ ≫ (ΓSpec.adjunction.unit.app X).val.c.app U =
      X.presheaf.map (homOfLE (by exact le_top)).op := by
  rw [← StructureSheaf.toOpen_res _ _ _ (homOfLE le_top), Category.assoc,
    NatTrans.naturality _ (homOfLE (le_top (a := U.unop))).op]
  show (ΓSpec.adjunction.counit.app (Scheme.Γ.rightOp.obj X)).unop ≫
    (Scheme.Γ.rightOp.map (ΓSpec.adjunction.unit.app X)).unop ≫ _ = _
  rw [← Category.assoc, ← unop_comp, ΓSpec.adjunction.left_triangle_components]
  dsimp
  exact Category.id_comp _
set_option maxHeartbeats 800000 in
@[reassoc]
theorem ΓSpec.toOpen_unit_app_val_c_app' {X : Scheme}
    (U : Opens (PrimeSpectrum (X.presheaf.obj (op ⊤)))) :
    StructureSheaf.toOpen (X.presheaf.obj (op ⊤)) U ≫
        (ΓSpec.adjunction.unit.app X).val.c.app (op U) =
      X.presheaf.map (homOfLE (by exact le_top)).op :=
  ΓSpec.toOpen_unit_app_val_c_app (op U)

lemma IsLocalization.bijective {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] (M : Submonoid R) [IsLocalization M S] [IsLocalization M T]
    (f : S →+* T) (hf : f.comp (algebraMap R S) = algebraMap R T) : Function.Bijective f :=
  (show f = IsLocalization.algEquiv M S T by
    apply IsLocalization.ringHom_ext M; rw [hf]; ext; simp) ▸
    (IsLocalization.algEquiv M S T).toEquiv.bijective

/-- If `U` is qcqs, then `Γ(X, D(f)) ≃ Γ(X, U)_f` for every `f : Γ(X, U)`.
This is known as the **Qcqs lemma** in [R. Vakil, *The rising sea*][RisingSea]. -/
theorem isIso_ΓSpec_adjunction_unit_app_basicOpen {X : Scheme} [CompactSpace X]
    [QuasiSeparatedSpace X] (f : X.presheaf.obj (op ⊤)) :
    IsIso ((ΓSpec.adjunction.unit.app X).val.c.app (op (PrimeSpectrum.basicOpen f))) := by
  refine @IsIso.of_isIso_comp_right _ _ _ _ _ _ (X.presheaf.map
    (eqToHom (ΓSpec.adjunction_unit_map_basicOpen _ _).symm).op) _ ?_
  rw [ConcreteCategory.isIso_iff_bijective, CommRingCat.forget_map]
  apply (config := { allowSynthFailures := true }) IsLocalization.bijective
  · exact StructureSheaf.IsLocalization.to_basicOpen _ _
  · refine is_localization_basicOpen_of_qcqs ?_ ?_ _
    · exact isCompact_univ
    · exact isQuasiSeparated_univ
  · rw [← CommRingCat.comp_eq_ring_hom_comp]
    simp [RingHom.algebraMap_toAlgebra]
    rw [ΓSpec.toOpen_unit_app_val_c_app'_assoc, ← Functor.map_comp]
    rfl

lemma iSup_basicOpen_eq_top_of_span_eq_top {X : Scheme} (s : Set (X.presheaf.obj (op ⊤)))
    (hs : Ideal.span s = ⊤) : (⨆ i ∈ s, X.basicOpen i) = ⊤ := by
  conv_rhs => rw [← Opens.map_top (ΓSpec.adjunction.unit.app X).1.base]
  rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [← ΓSpec.adjunction_unit_map_basicOpen]
  ext
  simp only [Opens.iSup_mk, Opens.carrier_eq_coe, Opens.map_coe, Opens.coe_mk, Set.mem_iUnion,
    Set.mem_preimage]

lemma isAffineOpen_of_isAffineOpen_basicOpen_aux (s : Set (X.presheaf.obj (op ⊤)))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    QuasiSeparatedSpace X := by
  rw [quasiSeparatedSpace_iff_affine]
  intros U V
  obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
  rw [← Set.inter_univ (_ ∩ _), ← Opens.coe_top, ← iSup_basicOpen_eq_top_of_span_eq_top _ e,
    ← iSup_subtype'', Opens.coe_iSup, Set.inter_iUnion]
  apply isCompact_iUnion
  intro i
  rw [Set.inter_inter_distrib_right]
  refine (hs₂ i (hs' i.2)).isQuasiSeparated _ _ Set.inter_subset_right
    (U.1.2.inter (X.basicOpen _).2) ?_ Set.inter_subset_right (V.1.2.inter (X.basicOpen _).2) ?_
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (U.2.basicOpenIsAffine _).isCompact
  · rw [← Opens.coe_inf, ← X.basicOpen_res _ (homOfLE le_top).op]
    exact (V.2.basicOpenIsAffine _).isCompact

lemma isAffineOpen_of_isAffineOpen_basicOpen (s : Set (X.presheaf.obj (op ⊤)))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, IsAffineOpen (X.basicOpen i)) :
    IsAffine X := by
  have : QuasiSeparatedSpace X := isAffineOpen_of_isAffineOpen_basicOpen_aux s hs hs₂
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff, ← Opens.coe_top, ← iSup_basicOpen_eq_top_of_span_eq_top _ e]
    simp only [Finset.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    apply s'.isCompact_biUnion
    exact fun i hi ↦ (hs₂ _ (hs' hi)).isCompact
  constructor
  have := (isomorphisms_isLocalAtTarget.openCover_TFAE (ΓSpec.adjunction.unit.app X)).out 0 5
  refine this.mpr ⟨s, fun i ↦ PrimeSpectrum.basicOpen i.1, ?_, ?_⟩
  · rw [PrimeSpectrum.iSup_basicOpen_eq_top_iff, Subtype.range_coe_subtype, Set.setOf_mem_eq, hs]
  · intro i
    apply (config := { allowSynthFailures := true }) isIso_of_isAffine_isIso
    · show IsAffineOpen (ΓSpec.adjunction.unit.app X ⁻¹ᵁ PrimeSpectrum.basicOpen i.1)
      rw [ΓSpec.adjunction_unit_map_basicOpen]
      exact hs₂ _ i.2
    · show IsAffineOpen _
      simp only [← basicOpen_eq_of_affine]
      exact (topIsAffineOpen (Scheme.Spec.obj (op _))).basicOpenIsAffine _
    · rw [morphismRestrict_c_app]
      apply (config := { allowSynthFailures := true }) IsIso.comp_isIso
      convert isIso_ΓSpec_adjunction_unit_app_basicOpen i.1 using 0
      refine congr(IsIso ((ΓSpec.adjunction.unit.app X).val.c.app (op $(?_))))
      rw [Opens.openEmbedding_obj_top]

lemma IsAffineHom.affineProperty_isLocal : affineProperty.IsLocal := by
  constructor
  · apply AffineTargetMorphismProperty.respectsIso_mk
    · rintro X Y Z e _ _ H
      have : IsAffine _ := H
      exact isAffineOfIso e.hom
    · exact fun _ _ _ ↦ id
  · intro X Y _ f r H
    have : IsAffine X := H
    show IsAffineOpen _
    rw [Scheme.preimage_basicOpen]
    exact (topIsAffineOpen X).basicOpenIsAffine _
  · intro X Y H f S hS hS'
    apply_fun Ideal.map (f.1.c.app (op ⊤)) at hS
    rw [Ideal.map_span, Ideal.map_top] at hS
    apply isAffineOpen_of_isAffineOpen_basicOpen _ hS
    have : ∀ i : S, IsAffineOpen (f⁻¹ᵁ Y.basicOpen i.1) := hS'
    simpa [Scheme.preimage_basicOpen] using this

open IsAffineHom in
lemma isAffineHom_isLocalAtTarget :
    PropertyIsLocalAtTarget @IsAffineHom :=
isAffineHom_eq_affineProperty ▸ affineProperty_isLocal.targetAffineLocallyIsLocal

lemma IsAffineHom.affineProperty_stableUnderBaseChange :
    affineProperty.StableUnderBaseChange := by
  introv X H
  delta affineProperty at H ⊢
  let H := H
  infer_instance

open IsAffineHom in
lemma isAffineHom_stableUnderBaseChange :
    MorphismProperty.StableUnderBaseChange @IsAffineHom :=
isAffineHom_eq_affineProperty ▸
  affineProperty_isLocal.stableUnderBaseChange affineProperty_stableUnderBaseChange

open IsAffineHom in
lemma isAffineHom_iff_isAffine [IsAffine Y] :
    IsAffineHom f ↔ IsAffine X :=
isAffineHom_eq_affineProperty ▸ affineProperty_isLocal.affine_target_iff f

instance (priority := 100) isAffineHom_of_isAffine [IsAffine X] [IsAffine Y] : IsAffineHom f :=
  (isAffineHom_iff_isAffine f).mpr inferInstance

lemma isAffine_of_isAffineHom [IsAffineHom f] [IsAffine Y] : IsAffine X :=
  (isAffineHom_iff_isAffine f).mp inferInstance

end AlgebraicGeometry

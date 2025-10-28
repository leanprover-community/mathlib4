/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# Quasi-affine schemes

## Main results
- `IsQuasiAffine`:
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
  This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion. -/
@[stacks 01P6]
class IsQuasiAffine (X : Scheme.{u}) : Prop extends
  CompactSpace X, IsImmersion X.toSpecΓ

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := low) [IsAffine X] : X.IsQuasiAffine where

instance (priority := low) [X.IsQuasiAffine] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from X.toSpecΓ]
    infer_instance

instance [X.IsQuasiAffine] : IsOpenImmersion X.toSpecΓ := by
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

/-- Any quasicompact locally closed subscheme of a quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  have : IsImmersion (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  constructor

lemma IsQuasiAffine.isBasis_basicOpen (X : Scheme.{u}) [IsQuasiAffine X] :
    Opens.IsBasis { X.basicOpen r | (r : Γ(X, ⊤)) (_ : IsAffineOpen (X.basicOpen r)) } := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ := (PrimeSpectrum.isBasis_basic_opens
    (R := Γ(X, ⊤))).exists_subset_of_mem_open (Set.mem_image_of_mem _ hxU) (X.toSpecΓ ''ᵁ U).2
  simp_rw [← toSpecΓ_preimage_basicOpen]
  refine ⟨_, ⟨r, ?_, rfl⟩, hxr, (Set.preimage_mono hrU).trans_eq
    (Set.preimage_image_eq _ X.toSpecΓ.isEmbedding.injective)⟩
  rw [← Hom.isAffineOpen_iff_of_isOpenImmersion X.toSpecΓ]
  convert IsAffineOpen.Spec_basicOpen r
  exact SetLike.coe_injective (Set.image_preimage_eq_of_subset
    (hrU.trans (Set.image_subset_range _ _)))

/-- A quasi-compact scheme is quasi-affine if
it can be covered by affine basic opens of global sections. -/
lemma IsQuasiAffine.of_forall_exists_mem_basicOpen (X : Scheme.{u}) [CompactSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) :
    IsQuasiAffine X := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : QuasiSeparatedSpace X := by
    choose r hr hxr using H
    exact .of_isOpenCover (U := (X.basicOpen <| r ·))
      (eq_top_iff.mpr fun _ _ ↦ Opens.mem_iSup.mpr ⟨_, hxr _⟩)
      (fun _ ↦ isRetrocompact_basicOpen _) (fun x ↦ (hr _).isQuasiSeparated)
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  obtain ⟨r, hr, hxr⟩ := H x
  refine ⟨PrimeSpectrum.basicOpen r, (X.toSpecΓ_preimage_basicOpen r).ge hxr, ?_⟩
  suffices IsOpenImmersion ((X.basicOpen r).ι ≫ X.toSpecΓ) by
    convert this <;> rw [toSpecΓ_preimage_basicOpen]
  rw [← Opens.toSpecΓ_SpecMap_presheaf_map_top]
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  exact MorphismProperty.comp_mem _ hr.isoSpec.hom _ inferInstance (.of_isLocalization r)

lemma IsQuasiAffine.of_isAffineHom [IsAffineHom f] [Y.IsQuasiAffine] : X.IsQuasiAffine := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  refine .of_forall_exists_mem_basicOpen _ fun x ↦ ?_
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (IsQuasiAffine.isBasis_basicOpen
    Y).exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  refine ⟨f.appTop r, ?_⟩
  rw [← preimage_basicOpen_top]
  exact ⟨hr.preimage _, hxr⟩

/-- The affine basic opens of a quasi-affine scheme forms an open cover. -/
@[simps] def openCoverBasicOpenTop (X : Scheme.{u}) [X.IsQuasiAffine] :
    X.OpenCover where
  I₀ := Σ' (r : Γ(X, ⊤)), IsAffineOpen (X.basicOpen r)
  X r := X.basicOpen r.1
  f r := (X.basicOpen r.1).ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
      (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact ⟨⟨r, hr⟩, (X.basicOpen r).opensRange_ι.ge hxr⟩

/-- If `f : X ⟶ Y` is an affine morphism between quasi-affine schemes, then it is the pullback of
  `Spec Γ(X, ⊤) ⟶ Spec Γ(Y, ⊤)` along the open immersion `Y ⟶ Spec Γ(Y, ⊤)`. -/
lemma isPullback_toSpecΓ_toSpecΓ (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine] :
    IsPullback f X.toSpecΓ Y.toSpecΓ (Spec.map f.appTop) := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.IsQuasiAffine.of_isAffineHom f
  have (r : Γ(Y, ⊤)) :
      IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
        (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge) := by
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (f.appTop r)
    refine CommRingCat.isPushout_of_isLocalization f.appTop.hom (f.appLE (Y.basicOpen r)
      (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge).hom ?_ (.powers r)
    change CommRingCat.Hom.hom (Y.presheaf.map _ ≫ f.appLE _ _ _) =
      CommRingCat.Hom.hom (f.appTop ≫ X.presheaf.map _)
    rw [f.map_appLE, Scheme.Hom.appLE]
  refine isPullback_of_openCover _ _ _ _ Y.openCoverBasicOpenTop fun r ↦ ?_
  let e : pullback f (Y.basicOpen r.fst).ι ≅ Spec Γ(X, X.basicOpen (f.appTop r.1)) :=
    pullbackRestrictIsoRestrict _ _ ≪≫ X.isoOfEq (Scheme.preimage_basicOpen_top f r.1) ≪≫
    IsAffineOpen.isoSpec (by rw [← Scheme.preimage_basicOpen_top]; exact r.2.preimage f)
  refine .of_iso ((this r.1).op.map Scheme.Spec) e.symm r.2.isoSpec.symm (.refl _) (.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    dsimp [e, Scheme.Cover.pullbackHom, IsAffineOpen.isoSpec_hom, Scheme.Hom.appLE]
    simp only [homOfLE_leOfHom, Spec.map_comp, Category.assoc,
      Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Scheme.Opens.toSpecΓ_naturality]
    simp_rw [← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp [pullback.condition]
  · simp only [Iso.symm_hom, Iso.eq_inv_comp]
    simp [e, IsAffineOpen.isoSpec_hom]

lemma preimage_opensRange_toSpecΓ (f : X ⟶ Y) [IsAffineHom f] [X.IsQuasiAffine] [Y.IsQuasiAffine] :
    Spec.map f.appTop ⁻¹ᵁ Y.toSpecΓ.opensRange = X.toSpecΓ.opensRange := by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_toSpecΓ f) ⊤).symm

end AlgebraicGeometry.Scheme

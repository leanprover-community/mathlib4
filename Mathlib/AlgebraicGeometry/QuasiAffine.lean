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
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
Despite the definition, any quasi-compact locally closed subscheme of an affine scheme is
quasi-affine. See `IsQuasiAffine.of_isImmersion` -/
@[stacks 01P6]
class IsQuasiAffine (X : Scheme.{u}) : Prop extends
  CompactSpace X, IsOpenImmersion X.toSpecΓ

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance (priority := low) [IsAffine X] : X.IsQuasiAffine where

instance (priority := low) [X.IsQuasiAffine] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from X.toSpecΓ]
    infer_instance

/-- Any quasicompact locally closed subscheme of an quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : IsImmersion (X.toSpecΓ ≫ Spec.map (Hom.appTop f)) := by
    rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  have : QuasiCompact X.toSpecΓ := (quasiCompact_over_affine_iff _).mpr ‹_›
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

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

/-- A qcqs scheme is quasi-affine if it can be covered by affine basic opens of global sections. -/
lemma IsQuasiAffine.of_forall_exists_mem_basicOpen (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) :
    IsQuasiAffine X := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  refine IsOpenImmersion.of_forall_source_exists_preimage _ fun x ↦ ?_
  obtain ⟨r, hr, hxr⟩ := H x
  refine ⟨PrimeSpectrum.basicOpen r, (X.toSpecΓ_preimage_basicOpen r).ge hxr, ?_⟩
  suffices IsOpenImmersion ((X.basicOpen r).ι ≫ X.toSpecΓ) by
    convert this <;> rw [toSpecΓ_preimage_basicOpen]
  rw [← Opens.toSpecΓ_SpecMap_map_top]
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  refine MorphismProperty.comp_mem _ hr.isoSpec.hom _ inferInstance (.of_isLocalization r)

end AlgebraicGeometry.Scheme

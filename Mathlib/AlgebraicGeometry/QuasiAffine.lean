/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# Quasi-affine schemes

## Main results
- `IsQuasiAffine`:
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

open CategoryTheory Limits

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

/-- Superseded by `IsQuasiAffine.of_isImmersion`. -/
@[stacks 01P9]
private lemma IsQuasiAffine.of_isOpenImmersion [CompactSpace X]
    [Y.IsQuasiAffine] [IsOpenImmersion f] : X.IsQuasiAffine := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : X.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  apply IsOpenImmersion.of_forall_source_exists
  · refine .of_comp (f := (Spec.map f.appTop).base) ?_
    rw [← TopCat.coe_comp, ← comp_coeBase, ← toSpecΓ_naturality]
    exact (f ≫ Y.toSpecΓ).isOpenEmbedding.injective
  · intro x
    obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrf⟩ :=
      PrimeSpectrum.isBasis_basic_opens (R := Γ(Y, ⊤)).exists_subset_of_mem_open
      (by exact ⟨x, rfl⟩) (f ≫ Y.toSpecΓ).opensRange.2
    refine ⟨_, ((f ≫ Y.toSpecΓ) ⁻¹ᵁ (PrimeSpectrum.basicOpen r)).ι,
      inferInstance, by simpa using hxr, ?_⟩
    have := (f ≫ Y.toSpecΓ).isIso_app _ hrf
    have : IsIso (Spec.map f.appTop ∣_ PrimeSpectrum.basicOpen r) := by
      have : IsAffine (Scheme.Opens.toScheme (X := Spec _) (PrimeSpectrum.basicOpen r)) :=
        IsAffineOpen.Spec_basicOpen r
      refine (HasAffineProperty.iff_of_isAffine (P := .isomorphisms Scheme)).mpr
        ⟨(IsAffineOpen.Spec_basicOpen r).preimage (Spec.map _), ?_⟩
      simp only [morphismRestrict_app', TopologicalSpace.Opens.map_top]
      suffices ∀ (U : (Spec _).Opens) (hU : U = PrimeSpectrum.basicOpen r)
        (V : (Spec _).Opens) (hV : V = PrimeSpectrum.basicOpen (f.appTop r)),
        IsIso ((Spec.map f.appTop).appLE U V (by subst_vars; rfl)) from
        this _ (by simp) _ (by simp; rfl)
      rintro _ rfl _ rfl
      convert_to IsIso ((f ≫ Y.toSpecΓ).app (PrimeSpectrum.basicOpen r) ≫ X.presheaf.map (eqToHom
        (by simp only [preimage_comp, toSpecΓ_preimage_basicOpen, preimage_basicOpen_top])).op ≫
        inv (X.toSpecΓ.app (PrimeSpectrum.basicOpen (f.appTop r)))) using 1
      · rw [← Category.assoc, IsIso.eq_comp_inv]
        simp [Hom.app_eq_appLE, - comp_appLE, appLE_comp_appLE, toSpecΓ_naturality]
      · infer_instance
    convert_to IsOpenImmersion ((f ≫ Y.toSpecΓ) ∣_ _ ≫
      inv ((Spec.map (Hom.appTop f) ∣_ PrimeSpectrum.basicOpen r)) ≫ Scheme.Opens.ι _)
    · trans Scheme.homOfLE _ (by rw [← preimage_comp, toSpecΓ_naturality]) ≫ X.toSpecΓ ∣_ _ ≫
        (Spec.map f.appTop ⁻¹ᵁ PrimeSpectrum.basicOpen r).ι
      · simp
      · simp_rw [← Category.assoc, cancel_mono, IsIso.eq_comp_inv, ← cancel_mono (Scheme.Opens.ι _)]
        simp [toSpecΓ_naturality]
    · infer_instance

/-- Any quasicompact locally closed subscheme of an quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  wlog hY : IsAffine Y
  · refine @this _ _ (f ≫ Y.toSpecΓ) ?_ ?_ _ ?_ <;> clear this <;> infer_instance
  have : QuasiCompact f := by rwa [quasiCompact_over_affine_iff]
  have : IsAffine f.image :=
    HasAffineProperty.iff_of_isAffine.mp (inferInstanceAs (IsAffineHom f.imageι))
  exact .of_isOpenImmersion f.toImage

end AlgebraicGeometry.Scheme

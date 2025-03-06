/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.RingHom.Integral
import Mathlib.RingTheory.PolynomialAlgebra

/-!

# Integral morphisms of schemes

A morphism of schemes `f : X ⟶ Y` is integral if the preimage
of an arbitrary affine open subset of `Y` is affine and the induced ring map is integral.

It is equivalent to ask only that `Y` is covered by affine opens whose preimage is affine
and the induced ring map is integral.

-/

universe v u

open CategoryTheory TopologicalSpace Opposite MorphismProperty

namespace AlgebraicGeometry

/-- A morphism of schemes `X ⟶ Y` is finite if
the preimage of any affine open subset of `Y` is affine and the induced ring
hom is finite. -/
@[mk_iff]
class IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  integral_app (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral

namespace IsIntegralHom

instance hasAffineProperty : HasAffineProperty @IsIntegralHom
    fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom := by
  show HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
  rw [HasAffineProperty.affineAnd_iff _ RingHom.isIntegral_respectsIso
    RingHom.isIntegral_isStableUnderBaseChange.localizationPreserves.away
    RingHom.isIntegral_ofLocalizationSpan]
  simp [isIntegralHom_iff]

instance : IsStableUnderComposition @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderComposition (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_stableUnderComposition

instance : IsStableUnderBaseChange @IsIntegralHom :=
  HasAffineProperty.affineAnd_isStableUnderBaseChange (Q := RingHom.IsIntegral) hasAffineProperty
    RingHom.isIntegral_respectsIso RingHom.isIntegral_isStableUnderBaseChange

instance : ContainsIdentities @IsIntegralHom :=
  ⟨fun X ↦ ⟨fun _ _ ↦ by simpa using RingHom.isIntegral_of_surjective _ (Equiv.refl _).surjective⟩⟩

lemma SpecMap_iff {R S : CommRingCat} {φ : R ⟶ S} :
    IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom), and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowIsoΓSpecOfIsAffine φ).symm, inferInstance]

instance : IsMultiplicative @IsIntegralHom where

instance (priority := 100) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIntegralHom f] :
    UniversallyClosed f := by
  revert X Y f ‹IsIntegralHom f›
  rw [universallyClosed_eq, ← IsStableUnderBaseChange.universally_eq (P := @IsIntegralHom)]
  apply universally_mono
  intro X Y f
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsLocalAtTarget.iff_of_openCover (P := topologically _) Y.affineCover]
    exact fun a i ↦ this _ ⟨_, rfl⟩ (a i)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · intro H
    have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := topologically _) X.isoSpec.inv]
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv] at H
    exact this _ _ ⟨_, rfl⟩ H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [SpecMap_iff]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _

lemma iff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} :
    IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  clear * -
  wlog hY : ∃ R, Y = Spec R
  · rw [IsLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover]
    rw [IsLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) Y.affineCover] at H₁
    rw [IsLocalAtTarget.iff_of_openCover (P := @IsAffineHom) Y.affineCover] at H₂
    exact fun _ ↦ this inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S
  · have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv]
    exact this _ inferInstance inferInstance ⟨_, rfl⟩
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = f := ⟨_, Spec.map_preimage _⟩
  rw [SpecMap_iff]
  apply PrimeSpectrum.isIntegral_of_isClosedMap_comap_mapRingHom
  algebraize [φ.1, Polynomial.mapRingHom φ.1]
  haveI : IsScalarTower R (Polynomial R) (Polynomial S) :=
    .of_algebraMap_eq' (Polynomial.mapRingHom_comp_C _).symm
  refine H₁.out (Spec.map (CommRingCat.ofHom Polynomial.C))
    (Spec.map (CommRingCat.ofHom Polynomial.C)) (Spec.map _)
    (isPullback_Spec_map_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S))).flip

lemma eq_universallyClosed_inf_isAffineHom :
    @IsIntegralHom = (@UniversallyClosed ⊓ @IsAffineHom : MorphismProperty Scheme) := by
  ext
  exact iff_universallyClosed_and_isAffineHom

end IsIntegralHom

end AlgebraicGeometry

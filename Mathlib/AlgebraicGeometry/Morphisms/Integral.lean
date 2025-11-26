/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
import Mathlib.RingTheory.RingHom.Integral

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

/-- A morphism of schemes `X ⟶ Y` is integral if the preimage of any affine open subset of `Y` is
affine and the induced ring hom on sections is integral. -/
@[mk_iff]
class IsIntegralHom {X Y : Scheme} (f : X ⟶ Y) : Prop extends IsAffineHom f where
  isIntegral_app (f) (U : Y.Opens) (hU : IsAffineOpen U) : (f.app U).hom.IsIntegral

@[deprecated (since := "2025-10-15")]
alias IsIntegralHom.integral_app := IsIntegralHom.isIntegral_app

alias Scheme.Hom.isIntegral_app := IsIntegralHom.isIntegral_app

namespace IsIntegralHom

variable {X Y Z S : Scheme.{u}}

instance hasAffineProperty : HasAffineProperty @IsIntegralHom
    fun X _ f _ ↦ IsAffine X ∧ RingHom.IsIntegral (f.app ⊤).hom := by
  change HasAffineProperty @IsIntegralHom (affineAnd RingHom.IsIntegral)
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

instance (priority := low) (f : X ⟶ Y) [IsClosedImmersion f] : IsIntegralHom f where
  isIntegral_app U hU := (RingHom.Finite.of_surjective _ (f.app_surjective U hU)).to_isIntegral

instance : IsMultiplicative @IsIntegralHom where
  id_mem _ := inferInstance

instance (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom f] [IsIntegralHom g] : IsIntegralHom (f ≫ g) :=
  MorphismProperty.comp_mem _ _ _ ‹_› ‹_›

instance (f : X ⟶ S) (g : Y ⟶ S) [IsIntegralHom g] : IsIntegralHom (Limits.pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

instance (f : X ⟶ S) (g : Y ⟶ S) [IsIntegralHom f] : IsIntegralHom (Limits.pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

instance (f : X ⟶ Y) (V : Y.Opens) [IsIntegralHom f] : IsIntegralHom (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V

instance : MorphismProperty.HasOfPostcompProperty @IsIntegralHom @IsSeparated :=
  MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.mpr
    fun _ _ _ _ ↦ inferInstanceAs (IsIntegralHom _)

lemma of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [IsIntegralHom (f ≫ g)] [IsSeparated g] :
    IsIntegralHom f := MorphismProperty.of_postcomp _ _ g ‹_› ‹_›

lemma comp_iff {f : X ⟶ Y} {g : Y ⟶ Z} [IsIntegralHom g] :
    IsIntegralHom (f ≫ g) ↔ IsIntegralHom f :=
  ⟨fun _ ↦ .of_comp f g, fun _ ↦ inferInstance⟩

lemma SpecMap_iff {R S : CommRingCat} {φ : R ⟶ S} :
    IsIntegralHom (Spec.map φ) ↔ φ.hom.IsIntegral := by
  have := RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.isIntegral_respectsIso
  rw [HasAffineProperty.iff_of_isAffine (P := @IsIntegralHom), and_iff_right]
  exacts [MorphismProperty.arrow_mk_iso_iff (RingHom.toMorphismProperty RingHom.IsIntegral)
    (arrowIsoΓSpecOfIsAffine φ).symm, inferInstance]

instance : IsMultiplicative @IsIntegralHom where

instance (priority := 100) (f : X ⟶ Y) [IsIntegralHom f] :
    UniversallyClosed f := by
  revert X Y f ‹IsIntegralHom f›
  rw [universallyClosed_eq, ← IsStableUnderBaseChange.universally_eq (P := @IsIntegralHom)]
  apply universally_mono
  intro X Y f
  wlog hY : ∃ R, Y = Spec R generalizing X Y
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover,
      IsZariskiLocalAtTarget.iff_of_openCover (P := topologically _) Y.affineCover]
    exact fun a i ↦ this _ ⟨_, rfl⟩ (a i)
  obtain ⟨R, rfl⟩ := hY
  wlog hX : ∃ S, X = Spec S generalizing X
  · intro H
    have inst : IsAffine X := isAffine_of_isAffineHom f
    rw [← cancel_left_of_respectsIso (P := topologically _) X.isoSpec.inv]
    rw [← cancel_left_of_respectsIso (P := @IsIntegralHom) X.isoSpec.inv] at H
    exact this _ ⟨_, rfl⟩ H
  obtain ⟨S, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.map_surjective f
  rw [SpecMap_iff]
  exact PrimeSpectrum.isClosedMap_comap_of_isIntegral _

lemma iff_universallyClosed_and_isAffineHom {X Y : Scheme.{u}} {f : X ⟶ Y} :
    IsIntegralHom f ↔ UniversallyClosed f ∧ IsAffineHom f := by
  refine ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨H₁, H₂⟩ ↦ ?_⟩
  clear * -
  wlog hY : ∃ R, Y = Spec R
  · rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsIntegralHom) Y.affineCover]
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @UniversallyClosed) Y.affineCover] at H₁
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := @IsAffineHom) Y.affineCover] at H₂
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
    (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_of_isPushout R S (Polynomial R) (Polynomial S))).flip

lemma eq_universallyClosed_inf_isAffineHom :
    @IsIntegralHom = (@UniversallyClosed ⊓ @IsAffineHom : MorphismProperty Scheme) := by
  ext
  exact iff_universallyClosed_and_isAffineHom

end IsIntegralHom

end AlgebraicGeometry

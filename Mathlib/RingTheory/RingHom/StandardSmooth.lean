/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.RingHomProperties
import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Standard smooth ring homomorphisms

In this file we define standard smooth ring homomorphisms and show their
meta properties.

## Notes

This contribution was created as part of the AIM workshop "Formalizing algebraic geometry"
in June 2024.

-/

universe t t' w w' u v

variable (n m : ℕ)

open TensorProduct

namespace RingHom

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

/-- A ring homomorphism `R →+* S` is standard smooth if `S` is standard smooth as `R`-algebra. -/
def IsStandardSmooth (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmooth.{t, w} _ _ _ _ f.toAlgebra

/-- A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra. -/
def IsStandardSmoothOfRelativeDimension (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension.{t, w} n _ _ _ _ f.toAlgebra

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth (f : R →+* S)
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} n f) :
    IsStandardSmooth.{t, w} f :=
  letI : Algebra R S := f.toAlgebra
  letI : Algebra.IsStandardSmoothOfRelativeDimension.{t, w} n R S := hf
  Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

variable {n m}

variable (R) in
lemma IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 (RingHom.id R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.id R

lemma IsStandardSmoothOfRelativeDimension.equiv (e : R ≃+* S) :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 (e : R →+* S) :=
  letI : Algebra R S := e.toRingHom.toAlgebra
  Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

variable {T : Type*} [CommRing T]

lemma IsStandardSmooth.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmooth.{t', w'} g) (hf : IsStandardSmooth.{t, w} f) :
    IsStandardSmooth.{max t t', max w w'} (g.comp f) := by
  rw [IsStandardSmooth]
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsStandardSmooth R S := hf
  letI : Algebra.IsStandardSmooth S T := hg
  exact Algebra.IsStandardSmooth.trans R S T

lemma IsStandardSmoothOfRelativeDimension.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmoothOfRelativeDimension.{t', w'} n g)
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} m f) :
    IsStandardSmoothOfRelativeDimension.{max t t', max w w'} (n + m) (g.comp f) := by
  rw [IsStandardSmoothOfRelativeDimension]
  letI := f.toAlgebra
  letI := g.toAlgebra
  letI := (g.comp f).toAlgebra
  letI : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  letI : Algebra.IsStandardSmoothOfRelativeDimension m R S := hf
  letI : Algebra.IsStandardSmoothOfRelativeDimension n S T := hg
  exact Algebra.IsStandardSmoothOfRelativeDimension.trans m n R S T

lemma isStandardSmooth_stableUnderComposition :
    StableUnderComposition @IsStandardSmooth.{t, w} :=
  fun _ _ _ _ _ _ _ _ hf hg ↦ hg.comp hf

lemma isStandardSmooth_respectsIso : RespectsIso @IsStandardSmooth.{t, w} := by
  apply isStandardSmooth_stableUnderComposition.respectsIso
  introv
  exact (IsStandardSmoothOfRelativeDimension.equiv e).isStandardSmooth

lemma isStandardSmoothOfRelativeDimension_respectsIso :
    RespectsIso (@IsStandardSmoothOfRelativeDimension.{t, w} n) where
  left {R S T _ _ _} f e hf := by
    rw [← zero_add n]
    exact (IsStandardSmoothOfRelativeDimension.equiv e).comp hf
  right {R S T _ _ _} f e hf := by
    rw [← add_zero n]
    exact hf.comp (IsStandardSmoothOfRelativeDimension.equiv e)

lemma isStandardSmooth_stableUnderBaseChange : StableUnderBaseChange @IsStandardSmooth.{t, w} := by
  apply StableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmooth]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

variable (n)

lemma isStandardSmoothOfRelativeDimension_stableUnderBaseChange :
    StableUnderBaseChange (@IsStandardSmoothOfRelativeDimension.{t, w} n) := by
  apply StableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmoothOfRelativeDimension n S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmoothOfRelativeDimension]
      convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

section Localization

variable {Rᵣ Sᵣ : Type*} [CommRing Rᵣ] [CommRing Sᵣ] [Algebra R Rᵣ] [Algebra S Sᵣ]

lemma IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway (r : R)
    [IsLocalization.Away r Rᵣ] :
    IsStandardSmoothOfRelativeDimension.{0, 0} 0 (algebraMap R Rᵣ) := by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension, this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

variable {R S Rᵣ Sᵣ : Type u} [CommRing R] [CommRing S] [CommRing Rᵣ]
  [CommRing Sᵣ] [Algebra R Rᵣ] [Algebra S Sᵣ]
  (f : R →+* S) (M : Submonoid R) [IsLocalization M Rᵣ] [IsLocalization (M.map f) Sᵣ]

lemma IsStandardSmooth.isLocalization_map (hf : IsStandardSmooth.{t, w} f) :
    IsStandardSmooth.{t, w} (IsLocalization.map Sᵣ f M.le_comap_map : Rᵣ →+* Sᵣ) :=
  (isStandardSmooth_stableUnderBaseChange).isLocalization_map _ _ _ hf

lemma IsStandardSmoothOfRelativeDimension.isLocalization_map
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} n f) :
    IsStandardSmoothOfRelativeDimension.{t, w} n
      (IsLocalization.map Sᵣ f M.le_comap_map : Rᵣ →+* Sᵣ) :=
  (isStandardSmoothOfRelativeDimension_stableUnderBaseChange n).isLocalization_map _ _ _ hf

end Localization

end RingHom

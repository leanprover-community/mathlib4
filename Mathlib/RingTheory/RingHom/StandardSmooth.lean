/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.RingTheory.LocalProperties.Basic
import Mathlib.RingTheory.Smooth.StandardSmooth
import Mathlib.Tactic.Algebraize

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
@[algebraize RingHom.IsStandardSmooth.toAlgebra]
def IsStandardSmooth (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmooth.{t, w} _ _ _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic.-/
lemma IsStandardSmooth.toAlgebra {f : R →+* S} (hf : IsStandardSmooth.{t, w} f) :
    @Algebra.IsStandardSmooth.{t, w} R S _ _ f.toAlgebra := hf

/-- A ring homomorphism `R →+* S` is standard smooth of relative dimension `n` if
`S` is standard smooth of relative dimension `n` as `R`-algebra. -/
@[algebraize RingHom.IsStandardSmoothOfRelativeDimension.toAlgebra]
def IsStandardSmoothOfRelativeDimension (f : R →+* S) : Prop :=
  @Algebra.IsStandardSmoothOfRelativeDimension.{t, w} n _ _ _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic.-/
lemma IsStandardSmoothOfRelativeDimension.toAlgebra {f : R →+* S}
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} n f) :
    @Algebra.IsStandardSmoothOfRelativeDimension.{t, w} n R S _ _ f.toAlgebra := hf

lemma IsStandardSmoothOfRelativeDimension.isStandardSmooth (f : R →+* S)
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} n f) :
    IsStandardSmooth.{t, w} f := by
  algebraize [f]
  exact Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth n

variable {n m}

variable (R) in
lemma IsStandardSmoothOfRelativeDimension.id :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 (RingHom.id R) :=
  Algebra.IsStandardSmoothOfRelativeDimension.id R

lemma IsStandardSmoothOfRelativeDimension.equiv (e : R ≃+* S) :
    IsStandardSmoothOfRelativeDimension.{t, w} 0 (e : R →+* S) := by
  algebraize [e.toRingHom]
  exact Algebra.IsStandardSmoothOfRelativeDimension.of_algebraMap_bijective e.bijective

variable {T : Type*} [CommRing T]

lemma IsStandardSmooth.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmooth.{t', w'} g) (hf : IsStandardSmooth.{t, w} f) :
    IsStandardSmooth.{max t t', max w w'} (g.comp f) := by
  rw [IsStandardSmooth]
  algebraize [f, g, (g.comp f)]
  exact Algebra.IsStandardSmooth.trans.{t, t', w, w'} R S T

lemma IsStandardSmoothOfRelativeDimension.comp {g : S →+* T} {f : R →+* S}
    (hg : IsStandardSmoothOfRelativeDimension.{t', w'} n g)
    (hf : IsStandardSmoothOfRelativeDimension.{t, w} m f) :
    IsStandardSmoothOfRelativeDimension.{max t t', max w w'} (n + m) (g.comp f) := by
  rw [IsStandardSmoothOfRelativeDimension]
  algebraize [f, g, (g.comp f)]
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

lemma isStandardSmooth_isStableUnderBaseChange :
    IsStableUnderBaseChange @IsStandardSmooth.{t, w} := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmooth_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmooth R T := by
      rw [RingHom.IsStandardSmooth] at h; convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmooth S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmooth]; convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

variable (n)

lemma isStandardSmoothOfRelativeDimension_isStableUnderBaseChange :
    IsStableUnderBaseChange (@IsStandardSmoothOfRelativeDimension.{t, w} n) := by
  apply IsStableUnderBaseChange.mk
  · exact isStandardSmoothOfRelativeDimension_respectsIso
  · introv h
    replace h : Algebra.IsStandardSmoothOfRelativeDimension n R T := by
      rw [RingHom.IsStandardSmoothOfRelativeDimension] at h
      convert h; ext; simp_rw [Algebra.smul_def]; rfl
    suffices Algebra.IsStandardSmoothOfRelativeDimension n S (S ⊗[R] T) by
      rw [RingHom.IsStandardSmoothOfRelativeDimension]
      convert this; ext; simp_rw [Algebra.smul_def]; rfl
    infer_instance

lemma IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway {Rᵣ : Type*} [CommRing Rᵣ]
    [Algebra R Rᵣ] (r : R) [IsLocalization.Away r Rᵣ] :
    IsStandardSmoothOfRelativeDimension.{0, 0} 0 (algebraMap R Rᵣ) := by
  have : (algebraMap R Rᵣ).toAlgebra = ‹Algebra R Rᵣ› := by
    ext
    rw [Algebra.smul_def]
    rfl
  rw [IsStandardSmoothOfRelativeDimension, this]
  exact Algebra.IsStandardSmoothOfRelativeDimension.localization_away r

lemma isStandardSmooth_localizationPreserves : LocalizationPreserves IsStandardSmooth.{t, w} :=
  isStandardSmooth_isStableUnderBaseChange.localizationPreserves

lemma isStandardSmoothOfRelativeDimension_localizationPreserves :
    LocalizationPreserves (IsStandardSmoothOfRelativeDimension.{t, w} n) :=
  (isStandardSmoothOfRelativeDimension_isStableUnderBaseChange n).localizationPreserves

lemma isStandardSmooth_holdsForLocalizationAway :
    HoldsForLocalizationAway IsStandardSmooth.{0, 0} := by
  introv R h
  exact (IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r).isStandardSmooth

lemma isStandardSmoothOfRelativeDimension_holdsForLocalizationAway :
    HoldsForLocalizationAway (IsStandardSmoothOfRelativeDimension.{0, 0} 0) := by
  introv R h
  exact IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r

lemma isStandardSmooth_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway IsStandardSmooth.{0, 0} :=
  isStandardSmooth_stableUnderComposition.stableUnderCompositionWithLocalizationAway
    isStandardSmooth_holdsForLocalizationAway

lemma isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway :
    StableUnderCompositionWithLocalizationAway (IsStandardSmoothOfRelativeDimension.{0, 0} n) where
  left R S _ _ _ _ _ r _ _ hf :=
    have : (algebraMap R S).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway r
    add_zero n ▸ IsStandardSmoothOfRelativeDimension.comp hf this
  right _ S T _ _ _ _ s _ _ hf :=
    have : (algebraMap S T).IsStandardSmoothOfRelativeDimension 0 :=
      IsStandardSmoothOfRelativeDimension.algebraMap_isLocalizationAway s
    zero_add n ▸ IsStandardSmoothOfRelativeDimension.comp this hf

end RingHom

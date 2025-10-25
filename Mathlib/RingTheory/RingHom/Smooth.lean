/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.RingHom.FinitePresentation
import Mathlib.RingTheory.Smooth.Locus

/-!
# Smooth ring homomorphisms

In this file we define smooth ring homomorphisms and show their meta properties.

-/

universe u

variable {R S : Type*} [CommRing R] [CommRing S]

open TensorProduct

namespace RingHom

/-- A ring homomorphism `f : R →+* S` is formally smooth
if `S` is formally smooth as an `R` algebra. -/
@[algebraize RingHom.FormallySmooth.toAlgebra]
def FormallySmooth (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallySmooth R S

/-- Helper lemma for the `algebraize` tactic -/
lemma FormallySmooth.toAlgebra {f : R →+* S} (hf : FormallySmooth f) :
    @Algebra.FormallySmooth R S _ _ f.toAlgebra := hf

lemma formallySmooth_algebraMap [Algebra R S] :
    (algebraMap R S).FormallySmooth ↔ Algebra.FormallySmooth R S := by
  rw [FormallySmooth, toAlgebra_algebraMap]

lemma FormallySmooth.holdsForLocalizationAway : HoldsForLocalizationAway @FormallySmooth :=
  fun _ _ _ _ _ r _ ↦ formallySmooth_algebraMap.mpr <| .of_isLocalization (.powers r)

lemma FormallySmooth.stableUnderComposition : StableUnderComposition @FormallySmooth := by
  intro R S T _ _ _ f g hf hg
  algebraize [f, g, g.comp f]
  exact .comp R S T

lemma FormallySmooth.respectsIso : RespectsIso @FormallySmooth :=
  stableUnderComposition.respectsIso fun e ↦ holdsForLocalizationAway.of_bijective _ _ e.bijective

lemma FormallySmooth.isStableUnderBaseChange : IsStableUnderBaseChange @FormallySmooth := by
  refine .mk respectsIso ?_
  introv H
  rw [formallySmooth_algebraMap] at H ⊢
  infer_instance

lemma FormallySmooth.localizationPreserves : LocalizationPreserves @FormallySmooth :=
  isStableUnderBaseChange.localizationPreserves

/-- A ring homomorphism `f : R →+* S` is smooth if `S` is smooth as an `R` algebra. -/
@[algebraize RingHom.Smooth.toAlgebra]
def Smooth (f : R →+* S) : Prop :=
  letI : Algebra R S := f.toAlgebra
  Algebra.Smooth R S

/-- Helper lemma for the `algebraize` tactic -/
lemma Smooth.toAlgebra {f : R →+* S} (hf : Smooth f) :
    @Algebra.Smooth R _ S _ f.toAlgebra := hf

lemma smooth_algebraMap [Algebra R S] :
    (algebraMap R S).Smooth ↔ Algebra.Smooth R S := by
  rw [RingHom.Smooth, toAlgebra_algebraMap]

lemma smooth_def {f : R →+* S} : f.Smooth ↔ f.FormallySmooth ∧ f.FinitePresentation :=
  letI := f.toAlgebra
  Algebra.smooth_iff _ _

namespace Smooth

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]

lemma stableUnderComposition : StableUnderComposition Smooth := by
  convert RingHom.FormallySmooth.stableUnderComposition.and
    RingHom.finitePresentation_stableUnderComposition
  rw [smooth_def]

lemma isStableUnderBaseChange : IsStableUnderBaseChange Smooth := by
  convert RingHom.FormallySmooth.isStableUnderBaseChange.and
    RingHom.finitePresentation_isStableUnderBaseChange
  rw [smooth_def]

lemma holdsForLocalizationAway : HoldsForLocalizationAway Smooth := by
  introv R h
  rw [smooth_algebraMap]
  exact ⟨Algebra.FormallySmooth.of_isLocalization (.powers r),
    IsLocalization.Away.finitePresentation r⟩

variable (R) in
/-- The identity of a ring is smooth. -/
lemma id : RingHom.Smooth (RingHom.id R) :=
  holdsForLocalizationAway.containsIdentities R

/-- Composition of smooth ring homomorphisms is smooth. -/
lemma comp {f : R →+* S} {g : S →+* T} (hf : f.Smooth) (hg : g.Smooth) : (g.comp f).Smooth := by
  algebraize [f, g, g.comp f]
  exact Algebra.Smooth.comp R S T

lemma ofLocalizationSpanTarget : OfLocalizationSpanTarget Smooth := by
  introv R hs hf
  have : f.FinitePresentation :=
    finitePresentation_ofLocalizationSpanTarget _ s hs fun r ↦ (hf r).finitePresentation
  algebraize [f]
  refine ⟨?_, ‹_›⟩
  rw [← Algebra.smoothLocus_eq_univ_iff, ← Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_top,
    ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simp only [TopologicalSpace.Opens.coe_iSup, Set.iUnion_subset_iff,
    Algebra.basicOpen_subset_smoothLocus_iff, ← formallySmooth_algebraMap]
  exact fun r hr ↦ (hf ⟨r, hr⟩).1

/-- Smoothness is a local property of ring homomorphisms. -/
lemma propertyIsLocal : PropertyIsLocal Smooth where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).left
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalizationAway).right

end RingHom.Smooth

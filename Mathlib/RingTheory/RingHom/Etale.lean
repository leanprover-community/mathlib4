/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.RingTheory.Etale.Locus
public import Mathlib.RingTheory.RingHom.Smooth
public import Mathlib.RingTheory.RingHom.Unramified

/-!
# Étale ring homomorphisms

We show the meta properties of étale morphisms.
-/

@[expose] public section

universe u

namespace RingHom

variable {R S : Type*} [CommRing R] [CommRing S]

section FormallyEtale

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma FormallyEtale.stableUnderComposition : StableUnderComposition FormallyEtale := by
  introv R hf hg
  algebraize [f, g, (g.comp f)]
  exact Algebra.FormallyEtale.comp R S T

instance : Algebra.FormallyEtale R R := .of_formallyUnramified_and_formallySmooth

lemma FormallyEtale.of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.FormallyEtale := by
  algebraize [f]
  exact .of_equiv (.ofBijective (Algebra.ofId R S) hf)

lemma FormallyEtale.respectsIso : RespectsIso FormallyEtale :=
  stableUnderComposition.respectsIso fun e ↦ .of_bijective e.bijective

lemma FormallyEtale.isStableUnderBaseChange : IsStableUnderBaseChange FormallyEtale := by
  refine .mk respectsIso ?_
  introv H
  simp only [formallyEtale_algebraMap] at *
  infer_instance

lemma FormallyEtale.holdsForLocalization : HoldsForLocalization FormallyEtale := by
  introv R _
  simp only [formallyEtale_algebraMap] at *
  exact .of_isLocalization M

lemma FormallyEtale.ofLocalizationSpanTarget : OfLocalizationSpanTarget FormallyEtale := by
  introv R hs H
  algebraize [f]
  rw [← f.algebraMap_toAlgebra, formallyEtale_algebraMap, ← Algebra.etaleLocus_eq_univ_iff,
    ← Set.univ_subset_iff, ← TopologicalSpace.Opens.coe_top,
    ← PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs]
  simpa [-PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Algebra.basicOpen_subset_etaleLocus_iff,
    ← formallyEtale_algebraMap] using H

lemma FormallyEtale.propertyIsLocal : PropertyIsLocal FormallyEtale where
  localizationAwayPreserves := isStableUnderBaseChange.localizationPreserves.away
  ofLocalizationSpanTarget := ofLocalizationSpanTarget
  ofLocalizationSpan := ofLocalizationSpanTarget.ofLocalizationSpan
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalization.holdsForLocalizationAway).1
  StableUnderCompositionWithLocalizationAwayTarget :=
    (stableUnderComposition.stableUnderCompositionWithLocalizationAway
      holdsForLocalization.holdsForLocalizationAway).2

lemma FormallyEtale.formallyUnramified {f : R →+* S} (hf : f.FormallyEtale) :
    f.FormallyUnramified := by
  algebraize [f]; exact inferInstanceAs (Algebra.FormallyUnramified _ _)

lemma FormallyEtale.formallySmooth {f : R →+* S} (hf : f.FormallyEtale) :
    f.FormallySmooth := by
  algebraize [f]; exact inferInstanceAs (Algebra.FormallySmooth _ _)

end FormallyEtale
section Etale

/-- A ring hom `R →+* S` is étale, if `S` is an étale `R`-algebra. -/
@[algebraize RingHom.Etale.toAlgebra]
def Etale {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  @Algebra.Etale R S _ _ f.toAlgebra

/-- Helper lemma for the `algebraize` tactic -/
lemma Etale.toAlgebra {f : R →+* S} (hf : Etale f) :
    @Algebra.Etale R S _ _ f.toAlgebra := hf

variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)

lemma etale_algebraMap [Algebra R S] : (algebraMap R S).Etale ↔ Algebra.Etale R S := by
  rw [RingHom.Etale, toAlgebra_algebraMap]

lemma etale_iff_formallyUnramified_and_smooth : f.Etale ↔ f.FormallyUnramified ∧ f.Smooth := by
  algebraize [f]
  simp only [Etale, Smooth, FormallyUnramified]
  exact ⟨fun h ↦ ⟨inferInstance, inferInstance, inferInstance⟩,
    fun ⟨h1, h2⟩ ↦ ⟨.of_formallyUnramified_and_formallySmooth, inferInstance⟩⟩

lemma Etale.eq_formallyUnramified_and_smooth :
    @Etale = fun R S (_ : CommRing R) (_ : CommRing S) f ↦ f.FormallyUnramified ∧ f.Smooth := by
  ext
  rw [etale_iff_formallyUnramified_and_smooth]

lemma Etale.of_bijective {f : R →+* S} (hf : Function.Bijective f) : f.Etale := by
  rw [etale_iff_formallyUnramified_and_smooth]
  exact ⟨.of_surjective hf.2, .of_bijective hf⟩

lemma Etale.isStableUnderBaseChange : IsStableUnderBaseChange Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.isStableUnderBaseChange.and Smooth.isStableUnderBaseChange

lemma Etale.propertyIsLocal : PropertyIsLocal Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.propertyIsLocal.and Smooth.propertyIsLocal

lemma Etale.respectsIso : RespectsIso Etale :=
  propertyIsLocal.respectsIso

lemma Etale.ofLocalizationSpanTarget : OfLocalizationSpanTarget Etale :=
  propertyIsLocal.ofLocalizationSpanTarget

lemma Etale.ofLocalizationSpan : OfLocalizationSpan Etale :=
  propertyIsLocal.ofLocalizationSpan

lemma Etale.stableUnderComposition : StableUnderComposition Etale := by
  rw [eq_formallyUnramified_and_smooth]
  exact FormallyUnramified.stableUnderComposition.and Smooth.stableUnderComposition

end Etale

end RingHom

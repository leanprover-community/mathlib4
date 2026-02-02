/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Unramified.Locus
public import Mathlib.RingTheory.LocalProperties.Basic

/-!

# The meta properties of unramified ring homomorphisms.

-/

@[expose] public section

namespace RingHom

variable {R : Type*} {S : Type*} [CommRing R] [CommRing S]

/--
A ring homomorphism `R →+* A` is formally unramified if `Ω[A⁄R]` is trivial.
See `Algebra.FormallyUnramified`.
-/
@[algebraize Algebra.FormallyUnramified]
def FormallyUnramified (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.FormallyUnramified R S

lemma formallyUnramified_algebraMap [Algebra R S] :
    (algebraMap R S).FormallyUnramified ↔ Algebra.FormallyUnramified R S := by
  rw [FormallyUnramified, toAlgebra_algebraMap]

namespace FormallyUnramified

lemma of_surjective {f : R →+* S} (hf : Function.Surjective f) : f.FormallyUnramified := by
  algebraize [f]
  exact Algebra.FormallyUnramified.of_surjective (Algebra.ofId R S) hf

lemma stableUnderComposition :
    StableUnderComposition FormallyUnramified := by
  intro R S T _ _ _ f g _ _
  algebraize [f, g, g.comp f]
  exact .comp R S T

lemma respectsIso :
    RespectsIso FormallyUnramified := by
  refine stableUnderComposition.respectsIso ?_
  intro R S _ _ e
  exact .of_surjective e.surjective

lemma isStableUnderBaseChange :
    IsStableUnderBaseChange FormallyUnramified := by
  refine .mk respectsIso ?_
  introv H
  rw [formallyUnramified_algebraMap] at H ⊢
  infer_instance

lemma holdsForLocalizationAway :
    HoldsForLocalizationAway FormallyUnramified := by
  intro R S _ _ _ r _
  rw [formallyUnramified_algebraMap]
  exact .of_isLocalization (.powers r)

lemma ofLocalizationPrime :
    OfLocalizationPrime FormallyUnramified := by
  intro R S _ _ f H
  algebraize [f]
  rw [FormallyUnramified, ← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro x
  let Rₓ := Localization.AtPrime (x.asIdeal.comap f)
  let Sₓ := Localization.AtPrime x.asIdeal
  letI : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyUnramified Rₓ Sₓ := H _ _
  exact Algebra.FormallyUnramified.comp R Rₓ Sₓ

lemma ofLocalizationSpanTarget :
    OfLocalizationSpanTarget FormallyUnramified := by
  intro R S _ _ f s hs H
  algebraize [f]
  rw [FormallyUnramified, ← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ?_ hrx
  convert H ⟨r, hr⟩
  dsimp
  rw [← algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq,
    formallyUnramified_algebraMap]

lemma propertyIsLocal :
    PropertyIsLocal FormallyUnramified := by
  constructor
  · exact isStableUnderBaseChange.localizationPreserves.away
  · exact ofLocalizationSpanTarget
  · exact ofLocalizationSpanTarget.ofLocalizationSpan
      (stableUnderComposition.stableUnderCompositionWithLocalizationAway
          holdsForLocalizationAway).1
  · exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
        holdsForLocalizationAway).2

end RingHom.FormallyUnramified

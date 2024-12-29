/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.AlgebraicGeometry.PrimeSpectrum.Basic
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Support

/-!
# Unramified is a local property

## Main results
- `Algebra.unramifiedLocus` : The set of primes that is unramified over the base.
- `Algebra.basicOpen_subset_unramifiedLocus_iff` :
  `D(f)` is contained in the unramified locus if and only if `A_f` is unramified over `R`.
- `Algebra.unramifiedLocus_eq_univ_iff` :
  The unramified locus is the whole spectrum if and only if `A` is unramified over `R`.
- `Algebra.isOpen_unramifiedLocus` :
  If `A` is (essentially) of finite type over `R`, then the unramified locus is open.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra

/-- `Algebra.unramifiedLocus R A` is the set of primes `p` of `A`
such that `Aₚ` is formally unramified over `R`. -/
def unramifiedLocus : Set (PrimeSpectrum A) :=
  { p | Algebra.FormallyUnramified R (Localization.AtPrime p.asIdeal) }

variable {R A}

lemma unramifiedLocus_eq_compl_support :
    unramifiedLocus R A = (Module.support A (Ω[A⁄R]))ᶜ := by
  ext p
  simp only [Set.mem_compl_iff, Module.not_mem_support_iff]
  have := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyUnramified_iff _ _).trans this.subsingleton_congr.symm

lemma basicOpen_subset_unramifiedLocus_iff {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ unramifiedLocus R A ↔
      Algebra.FormallyUnramified R (Localization.Away f) := by
  rw [unramifiedLocus_eq_compl_support, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset, Algebra.formallyUnramified_iff]
  exact (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr

lemma unramifiedLocus_eq_univ_iff :
    unramifiedLocus R A = Set.univ ↔ Algebra.FormallyUnramified R A := by
  rw [unramifiedLocus_eq_compl_support, compl_eq_comm, Set.compl_univ, eq_comm,
    Module.support_eq_empty_iff, Algebra.formallyUnramified_iff]

lemma isOpen_unramifiedLocus [EssFiniteType R A] : IsOpen (unramifiedLocus R A) := by
  rw [unramifiedLocus_eq_compl_support, Module.support_eq_zeroLocus]
  exact (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl

end Algebra

lemma RingHom.ofLocalizationPrime_formallyUnramified :
    RingHom.OfLocalizationPrime RingHom.FormallyUnramified := by
  intros R S _ _ f H
  algebraize [f]
  rw [FormallyUnramified, ← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro x
  let Rₓ := Localization.AtPrime (x.asIdeal.comap f)
  let Sₓ := Localization.AtPrime x.asIdeal
  have := Algebra.FormallyUnramified.of_isLocalization (Rₘ := Rₓ) (x.asIdeal.comap f).primeCompl
  letI : Algebra Rₓ Sₓ := (Localization.localRingHom _ _ _ rfl).toAlgebra
  have : IsScalarTower R Rₓ Sₓ := .of_algebraMap_eq
    fun x ↦ (Localization.localRingHom_to_map _ _ _ rfl x).symm
  have : Algebra.FormallyUnramified Rₓ Sₓ := H _ _
  exact Algebra.FormallyUnramified.comp R Rₓ Sₓ

lemma RingHom.ofLocalizationSpanTarget_formallyUnramified :
    RingHom.OfLocalizationSpanTarget RingHom.FormallyUnramified := by
  intros R S _ _ f s hs H
  algebraize [f]
  rw [FormallyUnramified, ← Algebra.unramifiedLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  intro x
  obtain ⟨r, hr, hrx⟩ : ∃ r ∈ s, x ∈ PrimeSpectrum.basicOpen r := by
    simpa using (PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mpr hs).ge
      (TopologicalSpace.Opens.mem_top x)
  refine Algebra.basicOpen_subset_unramifiedLocus_iff.mpr ?_ hrx
  convert H ⟨r, hr⟩
  dsimp
  rw [← RingHom.algebraMap_toAlgebra f, ← IsScalarTower.algebraMap_eq,
    RingHom.formallyUnramified_algebraMap]

lemma RingHom.isLocal_formallyUnramified :
    RingHom.PropertyIsLocal RingHom.FormallyUnramified := by
  constructor
  · intro R S _ _ f r R' S' _ _ _ _ _ _ H
    algebraize [f, (algebraMap S S').comp f, IsLocalization.Away.map R' S' f r]
    have := Algebra.FormallyUnramified.of_isLocalization (Rₘ := S') (.powers (f r))
    have := Algebra.FormallyUnramified.comp R S S'
    have H : Submonoid.powers r ≤ (Submonoid.powers (f r)).comap f := by
      rintro x ⟨n, rfl⟩; exact ⟨n, by simp⟩
    have : IsScalarTower R R' S' := .of_algebraMap_eq' (IsLocalization.map_comp H).symm
    exact Algebra.FormallyUnramified.of_comp R R' S'
  · exact RingHom.ofLocalizationSpanTarget_formallyUnramified
  · exact RingHom.ofLocalizationSpanTarget_formallyUnramified.ofLocalizationSpan
      (RingHom.stableUnderComposition_formallyUnramified
        |>.stableUnderCompositionWithLocalizationAway
          RingHom.holdsForLocalizationAway_formallyUnramified).1
  · exact (RingHom.stableUnderComposition_formallyUnramified
      |>.stableUnderCompositionWithLocalizationAway
        RingHom.holdsForLocalizationAway_formallyUnramified).2

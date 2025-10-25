/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Support

/-!
# Smooth locus of an algebra

Most results in this file are proved for algebras of finite presentations.
Some of them are true for arbitrary algebras but the proof is substantially harder.

## Main results
- `Algebra.smoothLocus` : The set of primes that are smooth over the base.
- `Algebra.basicOpen_subset_smoothLocus_iff` :
  `D(f)` is contained in the smooth locus if and only if `A_f` is smooth over `R`.
- `Algebra.smoothLocus_eq_univ_iff` :
  The smooth locus is the whole spectrum if and only if `A` is smooth over `R`.
- `Algebra.isOpen_smoothLocus` : The smooth locus is open.
-/

universe u

variable (R A : Type*) [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra

variable {A} in
/--
An `R`-algebra `A` is smooth at a prime `p` of `A` if `Aₚ` is formally smooth over `R`.

This does not imply `Aₚ` is smooth over `R` under the mathlib definition
even if `A` is finitely presented,
but it can be shown that this is equivalent to the stacks project definition that `A` is smooth
at `p` if and only if there exists `f ∉ p` such that `A_f` is smooth over `R`.
See `Algebra.basicOpen_subset_smoothLocus_iff_smooth` and `Algebra.isOpen_smoothLocus`.
-/
@[stacks 00TB]
abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop :=
  Algebra.FormallySmooth R (Localization.AtPrime p)

/-- `Algebra.smoothLocus R A` is the set of primes `p` of `A`
such that `Aₚ` is formally smooth over `R`. -/
def smoothLocus : Set (PrimeSpectrum A) := { p | IsSmoothAt R p.asIdeal }

variable {R A}

attribute [local instance] Module.finitePresentation_of_projective in
lemma smoothLocus_eq_compl_support_inter [EssFiniteType R A] :
    smoothLocus R A = (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A Ω[A⁄R] := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff,
    Module.mem_freeLocus]
  refine (Algebra.formallySmooth_iff _ _).trans (and_comm.trans ?_)
  congr! 1
  · have := IsLocalizedModule.iso p.asIdeal.primeCompl
      (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
    exact this.subsingleton_congr.symm
  · trans Module.Free (Localization.AtPrime p.asIdeal) Ω[Localization.AtPrime p.asIdeal⁄R]
    · have : EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        .of_isLocalization _ p.asIdeal.primeCompl
      have : EssFiniteType R (Localization.AtPrime p.asIdeal) := .comp _ A _
      exact ⟨fun _ ↦ Module.free_of_flat_of_isLocalRing, fun _ ↦ inferInstance⟩
    · have := IsLocalizedModule.iso p.asIdeal.primeCompl
        (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
      have := this.extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
      exact ⟨fun H ↦ H.of_equiv' this.symm, fun H ↦ H.of_equiv' this⟩

lemma basicOpen_subset_smoothLocus_iff [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ smoothLocus R A ↔
      Algebra.FormallySmooth R (Localization.Away f) := by
  rw [smoothLocus_eq_compl_support_inter, Set.subset_inter_iff, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset,
    Algebra.formallySmooth_iff, iff_comm, and_comm]
  congr! 1
  · have := IsLocalizedModule.iso (.powers f) (H1Cotangent.map R R A (Localization.Away f))
    rw [this.subsingleton_congr]
  · rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Module.basicOpen_subset_freeLocus_iff]
    have := IsLocalizedModule.iso (.powers f)
        (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    exact ⟨fun _ ↦ .of_equiv this.symm, fun _ ↦ .of_equiv this⟩

lemma basicOpen_subset_smoothLocus_iff_smooth [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ smoothLocus R A ↔
      Algebra.Smooth R (Localization.Away f) := by
  have : FinitePresentation A (Localization.Away f) := IsLocalization.Away.finitePresentation f
  rw [basicOpen_subset_smoothLocus_iff]
  exact ⟨fun H ↦ ⟨H, .trans _ A _⟩, fun H ↦ H.1⟩

lemma smoothLocus_eq_univ_iff [FinitePresentation R A] :
    smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A := by
  have := IsLocalization.atUnits A (.powers 1) (S := Localization.Away (1 : A)) (by simp)
  rw [Algebra.FormallySmooth.iff_of_equiv (this.restrictScalars R),
    ← basicOpen_subset_smoothLocus_iff]
  simp

lemma smoothLocus_comap_of_isLocalization {Af : Type*} [CommRing Af] [Algebra A Af] [Algebra R Af]
    [IsScalarTower R A Af] (f : A) [IsLocalization.Away f Af] :
    PrimeSpectrum.comap (algebraMap A Af) ⁻¹' smoothLocus R A = smoothLocus R Af := by
  ext p
  let q := PrimeSpectrum.comap (algebraMap A Af) p
  have : IsLocalization.AtPrime (Localization.AtPrime p.asIdeal) q.asIdeal :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization (.powers f) _ p.asIdeal
  refine Algebra.FormallySmooth.iff_of_equiv ?_
  exact (IsLocalization.algEquiv q.asIdeal.primeCompl _ _).restrictScalars R

-- Note that this does not follow directly from `smoothLocus_eq_compl_support_inter` because
-- `H¹(L_{S/R})` is not necessarily finitely generated.
open PrimeSpectrum in
lemma isOpen_smoothLocus [FinitePresentation R A] : IsOpen (smoothLocus R A) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    isBasis_basic_opens.exists_subset_of_mem_open
    (smoothLocus_eq_compl_support_inter.le hx).2 Module.isOpen_freeLocus
  rw [Module.basicOpen_subset_freeLocus_iff] at hf
  let Af := Localization.Away f
  have : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    .trans _ A _
  have : IsOpen (smoothLocus R Af) := by
    have := IsLocalizedModule.iso (.powers f)
      (KaehlerDifferential.map R R A (Localization.Away f))
    have := this.extendScalarsOfIsLocalization (.powers f) (Localization.Away f)
    have := Module.Projective.of_equiv this
    rw [smoothLocus_eq_compl_support_inter, Module.support_eq_zeroLocus]
    exact (isClosed_zeroLocus _).isOpen_compl.inter Module.isOpen_freeLocus
  rw [← smoothLocus_comap_of_isLocalization f] at this
  replace this := (PrimeSpectrum.localization_away_isOpenEmbedding Af f).isOpenMap _ this
  rw [Set.image_preimage_eq_inter_range, localization_away_comap_range Af f] at this
  exact ⟨_, Set.inter_subset_left, this, hx, hxf⟩

end Algebra

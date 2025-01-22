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

Most results are only valid for algebras of finite presentations.

## Main results
- `Algebra.smoothLocus` : The set of primes that is smooth over the base.
- `Algebra.basicOpen_subset_smoothLocus_iff` :
  `D(f)` is contained in the smooth locus if and only if `A_f` is smooth over `R`.
- `Algebra.smoothLocus_eq_univ_iff` :
  The smooth locus is the whole spectrum if and only if `A` is smooth over `R`.
- `Algebra.isOpen_smoothLocus` : The smooth locus is open.
-/

universe u

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

namespace Algebra

variable {A} in
/-- An `R`-algebra `A` is smooth at a prime `p` of `A` if `Aₚ` is formally smooth over `R`. -/
abbrev IsSmoothAt (p : Ideal A) [p.IsPrime] : Prop :=
  Algebra.FormallySmooth R (Localization.AtPrime p)

/-- `Algebra.smoothLocus R A` is the set of primes `p` of `A`
such that `Aₚ` is formally smooth over `R`. -/
def smoothLocus : Set (PrimeSpectrum A) := { p | IsSmoothAt R p.asIdeal }

variable {R A}

attribute [local instance] Module.finitePresentation_of_projective in
lemma smoothLocus_eq_compl_support_inter [EssFiniteType R A] :
    smoothLocus R A = (Module.support A (H1Cotangent R A))ᶜ ∩ Module.freeLocus A (Ω[A⁄R]) := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.not_mem_support_iff,
    Module.mem_freeLocus]
  refine Algebra.FormallySmooth.iff_subsingleton_and_projective.trans ?_
  congr! 1
  · have := IsLocalizedModule.iso p.asIdeal.primeCompl
      (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
    exact this.subsingleton_congr.symm
  · trans Module.Free (Localization.AtPrime p.asIdeal) (Ω[Localization.AtPrime p.asIdeal⁄R])
    · have : EssFiniteType A (Localization.AtPrime p.asIdeal) :=
        .of_isLocalization _ p.asIdeal.primeCompl
      have : EssFiniteType R (Localization.AtPrime p.asIdeal) := .comp _ A _
      exact ⟨fun _ ↦ Module.free_of_flat_of_isLocalRing, fun _ ↦ inferInstance⟩
    · have := IsLocalizedModule.iso p.asIdeal.primeCompl
        (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
      have := LinearEquiv.ofBijective (this.extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)) this.bijective
      exact ⟨fun H ↦ H.of_equiv' this.symm, fun H ↦ H.of_equiv' this⟩

lemma basicOpen_subset_smoothLocus_iff [FinitePresentation R A] {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ smoothLocus R A ↔
      Algebra.FormallySmooth R (Localization.Away f) := by
  rw [smoothLocus_eq_compl_support_inter, Set.subset_inter_iff, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset,
    Algebra.FormallySmooth.iff_subsingleton_and_projective]
  congr! 1
  · have := IsLocalizedModule.iso (.powers f) (H1Cotangent.map R R A (Localization.Away f))
    rw [this.subsingleton_congr]
  · rw [← PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Module.basicOpen_subset_freeLocus_iff]
    have := IsLocalizedModule.iso (.powers f)
        (KaehlerDifferential.map R R A (Localization.Away f))
    have := LinearEquiv.ofBijective (this.extendScalarsOfIsLocalization
      (.powers f) (Localization.Away f)) this.bijective
    exact ⟨fun _ ↦ .of_equiv this, fun _ ↦ .of_equiv this.symm⟩

lemma smoothLocus_eq_univ_iff [FinitePresentation R A] :
    smoothLocus R A = Set.univ ↔ Algebra.FormallySmooth R A := by
  have := IsLocalization.atUnits A (.powers 1) (S := Localization.Away (1 : A)) (by simp)
  rw [Algebra.FormallySmooth.iff_of_equiv (this.restrictScalars R),
    ← basicOpen_subset_smoothLocus_iff]
  simp

lemma isOpen_smoothLocus [FinitePresentation R A] : IsOpen (smoothLocus R A) := by
  rw [smoothLocus_eq_compl_support_inter, isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, hxf, hf⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hx.2 Module.isOpen_freeLocus
  rw [Module.basicOpen_subset_freeLocus_iff] at hf
  let Af := Localization.Away f
  obtain ⟨x, rfl⟩ := (PrimeSpectrum.localization_away_comap_range Af f).ge hxf
  have : Algebra.FinitePresentation A (Localization.Away f) :=
    IsLocalization.Away.finitePresentation f
  have : Algebra.FinitePresentation R (Localization.Away f) :=
    .trans _ A _
  have := IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))
  have := LinearEquiv.ofBijective (this.extendScalarsOfIsLocalization
    (.powers f) (Localization.Away f)) this.bijective
  have := Module.Projective.of_equiv this
  obtain ⟨_, ⟨_, ⟨g, rfl⟩, rfl⟩, hxg, hg⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (u := (Module.support (Localization.Away f) (H1Cotangent R (Localization.Away f)))ᶜ)
      (a := x) (by
        rw [Set.mem_compl_iff, Module.not_mem_support_iff]
        have := IsLocalizedModule.iso x.asIdeal.primeCompl
          (H1Cotangent.map R R Af (Localization.AtPrime x.asIdeal))
        refine this.subsingleton_congr.mpr ?_
        let e := (IsLocalization.localizationLocalizationAtPrimeIsoLocalization
          (.powers f) x.asIdeal).restrictScalars R
        refine (H1Cotangent.mapEquiv R _ _ e).subsingleton_congr.mp ?_
        have := IsLocalizedModule.iso (PrimeSpectrum.comap (algebraMap A Af) x).asIdeal.primeCompl
          (H1Cotangent.map R R A (Localization.AtPrime
            (PrimeSpectrum.comap (algebraMap A Af) x).asIdeal))
        refine this.subsingleton_congr.mp ?_
        exact Module.not_mem_support_iff.mp hx.1) (by
        rw [Module.support_eq_zeroLocus, isOpen_compl_iff]
        exact PrimeSpectrum.isClosed_zeroLocus _)
  rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.compl_subset_compl,
    ← LocalizedModule.subsingleton_iff_support_subset] at hg
  let Ag := Localization.Away g
  have := IsLocalizedModule.iso (.powers g) (H1Cotangent.map R R Af Ag)
  replace hg := this.subsingleton_congr.mp hg
  obtain ⟨g', ⟨_, n, rfl⟩, e⟩ := IsLocalization.mk'_surjective (.powers f) g
  have : IsLocalization.Away (f * g') Ag :=
    have : IsLocalization.Away (algebraMap A Af g') Ag :=
      .of_associated (r := g) ⟨(IsLocalization.Away.algebraMap_pow_isUnit f n).unit, by
        simp only [← e, IsUnit.unit_spec, ← map_pow, IsLocalization.mk'_spec_mk]⟩
    .mul' Af _ _ _
  refine ⟨PrimeSpectrum.basicOpen (f * g'), Set.subset_inter ?_ ?_,
    (PrimeSpectrum.basicOpen _).2, ?_⟩
  · rw [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.compl_subset_compl,
      ← LocalizedModule.subsingleton_iff_support_subset]
    have := IsLocalizedModule.iso (.powers (f * g'))
      (H1Cotangent.map R R A Ag)
    exact this.subsingleton_congr.mpr hg
  · rw [PrimeSpectrum.basicOpen_mul]
    refine Set.inter_subset_left.trans ?_
    rwa [Module.basicOpen_subset_freeLocus_iff]
  · simp only [PrimeSpectrum.basicOpen_eq_zeroLocus_compl, Set.mem_compl_iff,
      PrimeSpectrum.mem_zeroLocus, PrimeSpectrum.comap_asIdeal, Ideal.coe_comap,
      Set.singleton_subset_iff, Set.mem_preimage, SetLike.mem_coe, ← e, map_mul] at hxf hxg ⊢
    convert x.asIdeal.primeCompl.mul_mem (pow_mem hxf (n + 1)) hxg using 1
    rw [pow_succ', mul_assoc, ← map_pow, IsLocalization.mk'_spec' Af (y := ⟨_, _⟩)]
    rfl

end Algebra

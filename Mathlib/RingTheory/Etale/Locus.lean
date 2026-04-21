/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Smooth.Locus
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Etale locus of an algebra

## Main results
Let `A` be a `R`-algebra.
- `Algebra.etaleLocus` : The set of primes of `A` where it is étale over `R`.
- `Algebra.basicOpen_subset_etaleLocus_iff` :
  `D(f)` is contained in the etale locus if and only if `A_f` is formally etale over `R`.
- `Algebra.etaleLocus_eq_univ_iff` :
  The etale locus is the whole spectrum if and only if `A` is formally etale over `R`.
- `Algebra.isOpen_etaleLocus` :
  If `A` is of finite type over `R`, then the etale locus is open.
-/

@[expose] public section

namespace Algebra

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in
/-- We say that an `R`-algebra `A` is etale at a prime `q` of `A`
if `A_q` is formally etale over `R`. -/
abbrev IsEtaleAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyEtale R (Localization.AtPrime q)

variable (R A) in
/-- `Algebra.etaleLocus R A` is the set of primes `p` of `A` that are etale. -/
def etaleLocus : Set (PrimeSpectrum A) :=
  { p | IsEtaleAt R p.asIdeal }

@[simp]
lemma mem_etaleLocus_iff {p : PrimeSpectrum A} : p ∈ etaleLocus R A ↔ IsEtaleAt R p.asIdeal := .rfl

lemma IsEtaleAt.comp
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsEtaleAt R p] [IsEtaleAt A P] : IsEtaleAt R P := by
  have : FormallyEtale (Localization.AtPrime p) (Localization.AtPrime P) :=
    .localization_base p.primeCompl
  exact FormallyEtale.comp R (Localization.AtPrime p) _

lemma etaleLocus_eq_unramfiedLocus_inter_smoothLocus :
    etaleLocus R A = unramifiedLocus R A ∩ smoothLocus R A :=
  Set.ext fun _ ↦ FormallyEtale.iff_formallyUnramified_and_formallySmooth

lemma etaleLocus_eq_compl_support :
    etaleLocus R A = (Module.support A Ω[A⁄R])ᶜ ∩ (Module.support A (H1Cotangent R A))ᶜ := by
  ext p
  simp only [Set.mem_inter_iff, Set.mem_compl_iff, Module.notMem_support_iff]
  have h₁ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (KaehlerDifferential.map R R A (Localization.AtPrime p.asIdeal))
  have h₂ := IsLocalizedModule.iso p.asIdeal.primeCompl
    (H1Cotangent.map R R A (Localization.AtPrime p.asIdeal))
  exact (Algebra.formallyEtale_iff _ _).trans
    (and_congr h₁.subsingleton_congr.symm h₂.subsingleton_congr.symm)

lemma basicOpen_subset_etaleLocus_iff {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ etaleLocus R A ↔
      Algebra.FormallyEtale R (Localization.Away f) := by
  rw [etaleLocus_eq_compl_support, Set.subset_inter_iff, Set.subset_compl_comm,
    PrimeSpectrum.basicOpen_eq_zeroLocus_compl, compl_compl, Set.subset_compl_comm, compl_compl,
    ← LocalizedModule.subsingleton_iff_support_subset,
    ← LocalizedModule.subsingleton_iff_support_subset, formallyEtale_iff]
  exact and_congr (IsLocalizedModule.iso (.powers f)
    (KaehlerDifferential.map R R A (Localization.Away f))).subsingleton_congr
    (IsLocalizedModule.iso (.powers f)
      (H1Cotangent.map R R A (Localization.Away f))).subsingleton_congr

lemma etaleLocus_eq_univ_iff :
    etaleLocus R A = Set.univ ↔ Algebra.FormallyEtale R A := by
  rw [etaleLocus_eq_compl_support, ← Set.compl_union, compl_eq_comm, Set.compl_univ, eq_comm,
    ← Set.subset_empty_iff, Set.union_subset_iff, Set.subset_empty_iff, Set.subset_empty_iff,
    Module.support_eq_empty_iff, Module.support_eq_empty_iff, Algebra.formallyEtale_iff]

variable [FinitePresentation R A]

lemma isOpen_etaleLocus : IsOpen (etaleLocus R A) := by
  rw [etaleLocus_eq_unramfiedLocus_inter_smoothLocus]
  exact isOpen_unramifiedLocus.inter isOpen_smoothLocus

lemma basicOpen_subset_etaleLocus_iff_etale {f : A} :
    ↑(PrimeSpectrum.basicOpen f) ⊆ etaleLocus R A ↔ Algebra.Etale R (Localization.Away f) := by
  rw [basicOpen_subset_etaleLocus_iff]
  refine ⟨fun H ↦ ⟨H, inferInstance⟩, fun _ ↦ inferInstance⟩

lemma etaleLocus_eq_univ_iff_etale :
    etaleLocus R A = Set.univ ↔ Algebra.Etale R A := by
  rw [etaleLocus_eq_univ_iff]
  refine ⟨fun H ↦ ⟨H, inferInstance⟩, fun _ ↦ inferInstance⟩

lemma exists_etale_of_isEtaleAt
    (P : Ideal A) [P.IsPrime] [IsEtaleAt R P] :
    ∃ f ∉ P, Algebra.Etale R (Localization.Away f) := by
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hpr, hr⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show ⟨P, ‹_›⟩ ∈ etaleLocus R A by assumption) isOpen_etaleLocus
  exact ⟨r, hpr, ⟨basicOpen_subset_etaleLocus_iff.mp hr, .of_isLocalizationAway r⟩⟩

end Algebra

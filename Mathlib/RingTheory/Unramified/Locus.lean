/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Support

/-!
# Unramified locus of an algebra

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

namespace Algebra

section

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra A B]
    [Algebra R B] [IsScalarTower R A B]

variable (R) in
/-- We say that an `R`-algebra `A` is unramified at a prime `q` of `A`
if `A_q` is formally unramified over `R`.

If `A` is of finite type over `R` and `q` is lying over `p`, then this is equivalent to
`κ(q)/κ(p)` being separable and `pA_q = qA_q`.
See `Algebra.isUnramifiedAt_iff_map_eq` in `RingTheory.Unramified.LocalRing` -/
abbrev IsUnramifiedAt (q : Ideal A) [q.IsPrime] : Prop :=
  FormallyUnramified R (Localization.AtPrime q)

variable (R A) in
/-- `Algebra.unramifiedLocus R A` is the set of primes `p` of `A` that are unramified. -/
def unramifiedLocus : Set (PrimeSpectrum A) :=
  { p | IsUnramifiedAt R p.asIdeal }

lemma IsUnramifiedAt.comp
    (p : Ideal A) (P : Ideal B) [P.LiesOver p] [p.IsPrime] [P.IsPrime]
    [IsUnramifiedAt R p] [IsUnramifiedAt A P] : IsUnramifiedAt R P := by
  have : FormallyUnramified (Localization.AtPrime p) (Localization.AtPrime P) :=
    .of_comp A _ _
  exact FormallyUnramified.comp R (Localization.AtPrime p) _

variable (R) in
lemma IsUnramifiedAt.of_restrictScalars (P : Ideal B) [P.IsPrime]
    [IsUnramifiedAt R P] : IsUnramifiedAt A P :=
  FormallyUnramified.of_comp R _ _

end

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

lemma unramifiedLocus_eq_compl_support :
    unramifiedLocus R A = (Module.support A (Ω[A⁄R]))ᶜ := by
  ext p
  simp only [Set.mem_compl_iff, Module.notMem_support_iff]
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

end

end Algebra

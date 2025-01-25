/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wanyi He, Jiedong Jiang, Jingting Wang, Andrew Yang, Shouxin Zhang
-/
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
/-!
# The Properties of Minimal Primes Under Localization

In this file, we proved several properties concerning how the minimal primes above an ideal behaves
under localization.

## Main Results
- `Ideal.minimalPrimes_comap_subset`: For a ring homomorphism R →+* A and an ideal J of A, the
  minimal primes over the preimage of J is a subset of the preimages of the minimal primes over J.
- `IsLocalization.minimalPrimes_comap`: If A is a localization of R with respect to the submonoid S,
  J is an ideal of A, then the minimal primes over the preimage of J (under R →+* A) are exactly
  the preimages of the minimal primes over J.
- `IsLocalization.minimalPrimes_map`: If A is a localization of R with respect to the submonoid S,
  J is an ideal of R, then the minimal primes over the span of the image of J (under R →+* A) are
  exactly the ideals of A such that the preimage of which is a minimal prime over J.
-/

variable {R : Type*} [CommRing R]

theorem Ideal.minimalPrimes_comap_subset {A : Type*} [CommRing A] (f : R →+* A) (J : Ideal A) :
    (J.comap f).minimalPrimes ⊆ Ideal.comap f '' J.minimalPrimes :=
  fun p hp ↦ Ideal.exists_minimalPrimes_comap_eq f p hp

theorem IsLocalization.minimalPrimes_comap (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (J : Ideal A) :
    (J.comap (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A) '' J.minimalPrimes := by
  rcases eq_or_ne J ⊤ with (rfl | hJ)
  · simp_rw [Ideal.comap_top, Ideal.minimalPrimes_top, Set.image_empty]
  refine (Ideal.minimalPrimes_comap_subset _ _).antisymm ?_
  rintro _ ⟨p, hp, rfl⟩
  let i := IsLocalization.orderIsoOfPrime S A
  haveI := hp.1.1
  refine ⟨⟨Ideal.IsPrime.comap _ , Ideal.comap_mono hp.1.2⟩, fun q hq e => ?_⟩
  obtain ⟨⟨q', h₁⟩, h₂⟩ :=
    i.surjective ⟨q, hq.1, Set.disjoint_of_subset_right e (i ⟨_, hp.1.1⟩).2.2⟩
  replace h₂ : q'.comap (algebraMap R A) = q := by injection h₂
  subst h₂
  replace e := Ideal.map_mono (f := algebraMap R A) e
  replace hq := Ideal.map_mono (f := algebraMap R A) hq.2
  simp_rw [IsLocalization.map_comap S A] at e hq
  exact Ideal.comap_mono (hp.2 ⟨h₁, hq⟩ e)

theorem IsLocalization.minimalPrimes_map (S : Submonoid R) (A : Type*) [CommRing A]
    [Algebra R A] [IsLocalization S A] (J : Ideal R) :
    (J.map (algebraMap R A)).minimalPrimes = Ideal.comap (algebraMap R A)⁻¹' J.minimalPrimes := by
  ext p
  constructor
  · intro hp
    haveI := hp.1.1
    refine ⟨⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hp.1.2⟩, ?_⟩
    rintro I hI e
    have hI' : Disjoint (S : Set R) I := Set.disjoint_of_subset_right e
      ((IsLocalization.isPrime_iff_isPrime_disjoint S A _).mp hp.1.1).2
    refine (Ideal.comap_mono <|
      hp.2 ⟨?_, Ideal.map_mono hI.2⟩ (Ideal.map_le_iff_le_comap.mpr e)).trans_eq ?_
    · exact IsLocalization.isPrime_of_isPrime_disjoint S A I hI.1 hI'
    · exact IsLocalization.comap_map_of_isPrime_disjoint S A _ hI.1 hI'
  · intro hp
    refine ⟨⟨?_, Ideal.map_le_iff_le_comap.mpr hp.1.2⟩, ?_⟩
    · rw [IsLocalization.isPrime_iff_isPrime_disjoint S A,
        IsLocalization.disjoint_comap_iff S A]
      refine ⟨hp.1.1, ?_⟩
      rintro rfl
      exact hp.1.1.ne_top rfl
    · intro I hI e
      rw [← IsLocalization.map_comap S A I, ← IsLocalization.map_comap S A p]
      haveI := hI.1
      exact Ideal.map_mono (hp.2 ⟨Ideal.IsPrime.comap _, Ideal.map_le_iff_le_comap.mp hI.2⟩
        (Ideal.comap_mono e))

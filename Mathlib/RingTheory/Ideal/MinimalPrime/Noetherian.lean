/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/

module

public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.Noetherian.Defs

/-!

# Finiteness of minimal primes

We prove finiteness of minimal primes above an ideal.

This is proved without reference to `PrimeSpectrum` to avoid heavy imports.

-/

@[expose] public section

variable (R : Type*) [CommSemiring R] [hR : IsNoetherianRing R]

lemma Ideal.finite_minimalPrimes_of_isNoetherianRing (I : Ideal R) :
    I.minimalPrimes.Finite := by
  by_contra hI
  obtain ⟨I : Ideal R, hI : ¬ I.minimalPrimes.Finite, hmax⟩ :=
    set_has_maximal_iff_noetherian.mpr hR {I : Ideal R | ¬ I.minimalPrimes.Finite} ⟨I, hI⟩
  simp only [Set.mem_setOf_eq, not_imp_not] at hmax
  have h1 : ¬ I.IsPrime := by contrapose! hI; simp [minimalPrimes_eq_subsingleton_self]
  have h2 : I ≠ ⊤ := by contrapose! hI; simp [hI, minimalPrimes_top]
  obtain ⟨x, hx, y, hy, h⟩ := (not_isPrime_iff.mp h1).resolve_left h2
  rw [← Ideal.span_singleton_le_iff_mem, ← left_lt_sup] at hx hy
  refine hI (((hmax _ hx).union (hmax _ hy)).subset fun p ⟨⟨hp, hI⟩, hmin⟩ ↦ ?_)
  rcases hp.2 (hI h) with hxp | hyp
  · exact Or.inl ⟨⟨hp, sup_le hI (p.span_singleton_le_iff_mem.mpr hxp)⟩,
      fun q hq hqp ↦ hmin ⟨hq.1, hx.le.trans hq.2⟩ hqp⟩
  · exact Or.inr ⟨⟨hp, sup_le hI (p.span_singleton_le_iff_mem.mpr hyp)⟩,
      fun q hq hqp ↦ hmin ⟨hq.1, hy.le.trans hq.2⟩ hqp⟩

lemma minimalPrimes.finite_of_isNoetherianRing : (minimalPrimes R).Finite :=
  Ideal.finite_minimalPrimes_of_isNoetherianRing R ⊥

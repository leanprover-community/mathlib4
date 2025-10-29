/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.PrincipalIdealDomainOfPrime

/-!
# A Dedekind domain that is a UFD is a PID

In this file we show that a Dedekind domain that is a unique factorisation domain is also a
principal ideal domain.
-/

-- not an instance because this might cause a timeout
theorem IsPrincipalIdealRing.of_isDedekindDomain_of_uniqueFactorizationMonoid
    (R : Type*) [CommRing R] [IsDedekindDomain R] [UniqueFactorizationMonoid R] :
    IsPrincipalIdealRing R := by
  refine .of_prime_ne_bot fun P hp hp₀ ↦ ?_
  obtain ⟨x, hx₁, hx₂⟩ := hp.exists_mem_prime_of_ne_bot hp₀
  suffices Ideal.span {x} = P from this ▸ inferInstance
  have := (Ideal.span_singleton_prime hx₂.ne_zero).mpr hx₂
  exact (Ring.DimensionLeOne.prime_le_prime_iff_eq (by aesop)).mp <|
    P.span_singleton_le_iff_mem.mpr hx₁

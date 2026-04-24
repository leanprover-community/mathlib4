/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.RingTheory.DedekindDomain.Dvr
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Unramified.Field

/-!
# Unramified algebras over Dedekind domains

We prove that a domain finite and unramified over a Dedekind domain is a Dedekind domain.
-/

@[expose] public section

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B]

include A in
theorem isDedekindDomainDvr.of_formallyUnramified : IsDedekindDomainDvr B where
  __ := IsNoetherianRing.of_finite A B
  is_dvr_at_nonzero_prime := by
    intro q hq hqp
    let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
    suffices q'.IsPrincipal from ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
      (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
    let p := q.under A
    let := Localization.AtPrime.algebraOfLiesOver p q
    have : p.IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
    let : Field (A ⧸ p) := Ideal.Quotient.field p
    have := IsArtinianRing.of_finite (A ⧸ p) (B ⧸ p.map (algebraMap A B))
    suffices q' = (p.map (algebraMap A B)).map (algebraMap B (Localization.AtPrime q)) by
      rw [this, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
        ← Ideal.map_map]
      infer_instance
    rw [← (Algebra.FormallyUnramified.isRadical_map_isMaximal A B p).radical,
      IsLocalization.map_radical q.primeCompl,
      IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes (Localization.AtPrime q) q,
      Localization.AtPrime.map_eq_maximalIdeal]
    rw [Ideal.minimalPrimes_eq_comap]
    exact ⟨q.map (Ideal.Quotient.mk (p.map (algebraMap A B))),
      IsArtinianRing.mem_minimalPrimes bot_le, Ideal.comap_map_mk Ideal.map_comap_le⟩

include A in
/-- A domain finite and unramified over a Dedekind domain is a Dedekind domain. -/
theorem isDedekindDomain.of_formallyUnramified : IsDedekindDomain B :=
  have := isDedekindDomainDvr.of_formallyUnramified A B
  inferInstance

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

theorem isDedekindDomainDvr.of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [h0 : Algebra.FormallyUnramified A B] : IsDedekindDomainDvr B where
  __ := IsNoetherianRing.of_finite A B
  is_dvr_at_nonzero_prime := by
    intro q hq hqp
    have : (q.under A).IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
    have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (q.under A)
    let q' := IsLocalRing.maximalIdeal (Localization.AtPrime q)
    suffices q'.IsPrincipal from ((IsDiscreteValuationRing.TFAE (Localization.AtPrime q)
      (IsLocalization.AtPrime.not_isField B hq (Localization.AtPrime q))).out 4 0).mp this
    let p := q.under A
    let : Field (A ⧸ p) := Ideal.Quotient.field p
    let p' := p.map (algebraMap A B)
    let p'' := p'.map (algebraMap B (Localization.AtPrime q))
    suffices q' = p'' by
      simp_rw [this, p'', p', Ideal.map_map, ← IsScalarTower.algebraMap_eq,
        IsScalarTower.algebraMap_eq A (Localization.AtPrime p) (Localization.AtPrime q),
        ← Ideal.map_map]
      infer_instance
    let Q := B ⧸ p'
    have : IsArtinianRing Q := IsArtinianRing.of_finite (A ⧸ p) Q
    have h (I : Ideal Q) [I.IsPrime] : I.IsMaximal := IsArtinianRing.isMaximal_of_isPrime I
    replace h {I : Ideal B} (hp : p' ≤ I) [I.IsPrime] : I.IsMaximal := by
      rw [← Ideal.comap_map_mk hp]
      have := Ideal.isPrime_map_quotientMk_of_isPrime hp
      exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p') Ideal.Quotient.mk_surjective
    replace h {I} (hp : p' ≤ I) (hq : I ≤ q) [I.IsPrime] : I = q := (h hp).eq_of_le hqp.ne_top hq
    replace h {I} (hp : p'' ≤ I) (hq : I ≤ q') [I.IsPrime] : I = q' := by
      rw [← Localization.AtPrime.eq_maximalIdeal_iff_comap_eq]
      exact h (Ideal.map_le_iff_le_comap.mp hp)
        ((Ideal.comap_mono hq).trans_eq Localization.AtPrime.comap_maximalIdeal)
    replace h : p''.minimalPrimes = {q'} := by
      rw [Set.eq_singleton_iff_nonempty_unique_mem]
      refine ⟨?_, fun r hr ↦ have := hr.1.1; h hr.1.2 (IsLocalRing.le_maximalIdeal_of_isPrime r)⟩
      rw [Set.nonempty_iff_ne_empty, ne_eq, Ideal.minimalPrimes_eq_empty_iff]
      exact (IsLocalization.map_algebraMap_ne_top_iff_disjoint q.primeCompl _ p').mpr
        (Set.disjoint_compl_left_iff_subset.mpr Ideal.map_comap_le)
    have hp' : p'.IsRadical := Algebra.FormallyUnramified.map_isMaximal_isRadical A B p
    have hp'' : p''.IsRadical := by
      rw [← Ideal.radical_eq_iff] at hp' ⊢
      rw [← IsLocalization.map_radical q.primeCompl, hp']
    rw [← hp''.radical, ← Ideal.sInf_minimalPrimes, h, sInf_singleton]

/-- A domain finite and unramified over a Dedekind domain is a Dedekind domain. -/
theorem isDedekindDomain.of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] : IsDedekindDomain B :=
  have := isDedekindDomainDvr.of_formallyUnramified A B
  inferInstance

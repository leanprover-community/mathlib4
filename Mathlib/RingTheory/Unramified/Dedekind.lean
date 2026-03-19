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

section temp

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S] [Algebra R S]
  [IsLocalization M S]

include M in
theorem IsLocalization.comap_le_comap_iff {I J : Ideal S} :
    I.comap (algebraMap R S) ≤ J.comap (algebraMap R S) ↔ I ≤ J := by
  exact (IsLocalization.orderEmbedding M S).le_iff_le

include M in
theorem IsLocalization.comap_lt_comap_iff {I J : Ideal S} :
    I.comap (algebraMap R S) < J.comap (algebraMap R S) ↔ I < J := by
  exact (IsLocalization.orderEmbedding M S).lt_iff_lt

include M in
theorem IsLocalization.isMaximal_of_isMaximal_comap
    {I : Ideal S} (h : (I.comap (algebraMap R S)).IsMaximal) :
    I.IsMaximal := by
  rw [Ideal.isMaximal_def, isCoatom_iff_ge_of_le] at h ⊢
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa using h1, fun J h3 h4 ↦ ?_⟩
  specialize h2 (J.comap (algebraMap R S)) (by simpa)
  simp_rw [IsLocalization.comap_le_comap_iff M S] at h2
  exact h2 h4

end temp

section temp

variable {R : Type*} [CommRing R] (M : Submonoid R) (S : Type*) [CommRing S] [Algebra R S]

theorem IsLocalization.minimalPrimes_map_of_isArtinian (q : Ideal R) [q.IsPrime]
    [IsLocalization q.primeCompl S] (I : Ideal R) [IsArtinianRing (R ⧸ I)] (h : I ≤ q) :
    haveI : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
    (I.map (algebraMap R S)).minimalPrimes = {IsLocalRing.maximalIdeal S} := by
  rw [Set.eq_singleton_iff_nonempty_unique_mem]
  constructor
  · simp_rw [Set.nonempty_iff_ne_empty, ne_eq, Ideal.minimalPrimes_eq_empty_iff,
      IsLocalization.map_algebraMap_ne_top_iff_disjoint q.primeCompl S]
    exact Set.disjoint_compl_left_iff_subset.mpr h
  · intro r hr
    have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S q
    apply IsLocalRing.eq_maximalIdeal
    apply IsLocalization.isMaximal_of_isMaximal_comap q.primeCompl
    rw [IsLocalization.minimalPrimes_map q.primeCompl, Set.mem_preimage,
      ← Ideal.mk_ker (I := I), RingHom.ker_eq_comap_bot] at hr
    obtain ⟨s, hs, hs'⟩ := Ideal.exists_minimalPrimes_comap_eq _ _ hr
    replace hs : s.IsPrime := hs.1.1
    replace hs : s.IsMaximal := IsArtinianRing.isMaximal_of_isPrime s
    rw [← hs']
    exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective

end temp

theorem isReduced_quotient_iff_isRadical (R : Type*) [CommRing R] (I : Ideal R) :
    IsReduced (R ⧸ I) ↔ I.IsRadical := by
  rw [← I.mk_ker, RingHom.ker_isRadical_iff_reduced_of_surjective, I.mk_ker]
  · rfl
  · exact Ideal.Quotient.mk_surjective

theorem formallyUnramified_quotient (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.FormallyUnramified A B]
    (p : Ideal A) :
    Algebra.FormallyUnramified (A ⧸ p) (B ⧸ p.map (algebraMap A B)) := by
  let q := p.map (algebraMap A B)
  let Q := B ⧸ q
  let Q' := TensorProduct A (A ⧸ p) B
  let e1 : Q ≃+* Q' := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ p)).toRingEquiv
  let e2 : Q ≃ₐ[A] Q' :=
  { __ := e1
    commutes' x := by
      rw [IsScalarTower.algebraMap_apply A B Q]
      simp [e1, Q, -Ideal.Quotient.mk_algebraMap]
      rw [Algebra.TensorProduct.quotIdealMapEquivTensorQuot_mk]
      simp [Q', ← Algebra.TensorProduct.tmul_one_eq_one_tmul]
       }
  let e3: Q ≃ₐ[A ⧸ p] Q' := e2.extendScalarsOfSurjective (by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective)
  have : Algebra.FormallyUnramified (A ⧸ p) Q' := Algebra.FormallyUnramified.base_change (A ⧸ p)
  exact this.of_equiv e3.symm

theorem map_isMaximal_isRadical_of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [Algebra.FormallyUnramified A B]
    (p : Ideal A) [p.IsMaximal] : (p.map (algebraMap A B)).IsRadical := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let p' := p.map (algebraMap A B)
  let Q := B ⧸ p'
  rw [← isReduced_quotient_iff_isRadical]
  -- todo: golf with formallyUnramified_quotient
  let Q' := TensorProduct A (A ⧸ p) B
  let e : Q ≃+* Q' := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ p)).toRingEquiv
  have : Algebra.FormallyUnramified (A ⧸ p) Q := formallyUnramified_quotient A B p
  have : IsReduced Q' := Algebra.FormallyUnramified.isReduced_of_field (A ⧸ p) Q'
  exact isReduced_of_injective e e.injective

theorem isDedekindDomainDvr.of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] : IsDedekindDomainDvr B where
  __ := IsNoetherianRing.of_finite A B
  is_dvr_at_nonzero_prime := by
    intro q hq hqp
    have : (q.under A).IsMaximal := (hqp.under A).isMaximal (q.under_ne_bot A hq)
    have : q.IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal q (q.under A)
    suffices IsDiscreteValuationRing (Localization.AtPrime q) from inferInstance
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
      apply Submodule.IsPrincipal.map_ringHom
      infer_instance
    -- suffices p''.IsMaximal from (IsLocalRing.eq_maximalIdeal this).symm
    let Q := B ⧸ p'
    have : IsArtinianRing Q := IsArtinianRing.of_finite (A ⧸ p) Q
    have h : p'.IsRadical := map_isMaximal_isRadical_of_formallyUnramified A B p
    replace h : p''.IsRadical := by
      rw [← Ideal.radical_eq_iff] at h ⊢
      rw [← IsLocalization.map_radical q.primeCompl, h]
    -- have : IsArtinianRing (B ⧸ q) := by
    --   have h : p' ≤ q := Ideal.map_comap_le
    --   exact Function.Surjective.isArtinianRing (Ideal.Quotient.factor_surjective h)
    -- have : IsArtinianRing (Localization.AtPrime q ⧸ q') :=
    --   (IsLocalization.AtPrime.equivQuotMaximalIdeal q (Localization.AtPrime q)).isArtinianRing
    suffices p''.minimalPrimes = {q'} by
      rw [← h.radical, ← Ideal.sInf_minimalPrimes, this, sInf_singleton]
    exact IsLocalization.minimalPrimes_map_of_isArtinian (Localization.AtPrime q) q p'
      Ideal.map_comap_le

/-- A domain finite and unramified over a Dedekind domain is a Dedekind domain. -/
theorem isDedekindDomain.of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] : IsDedekindDomain B :=
  have := isDedekindDomainDvr.of_formallyUnramified A B
  inferInstance

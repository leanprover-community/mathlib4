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

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*)
  [CommSemiring S] [Algebra R S] [IsLocalization M S]

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

theorem isReduced_quotient_iff_isRadical (R : Type*) [CommRing R] (I : Ideal R) :
    IsReduced (R ⧸ I) ↔ I.IsRadical := by
  rw [← I.mk_ker, RingHom.ker_isRadical_iff_reduced_of_surjective, I.mk_ker]
  · rfl
  · exact Ideal.Quotient.mk_surjective

theorem map_isMaximal_isRadical_of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsNoetherianRing A] [Algebra.FormallyUnramified A B]
    (p : Ideal A) [p.IsMaximal] : (p.map (algebraMap A B)).IsRadical := by
  let : Field (A ⧸ p) := Ideal.Quotient.field p
  let p' := p.map (algebraMap A B)
  let Q := B ⧸ p'
  have : IsArtinianRing Q := IsArtinianRing.of_finite (A ⧸ p) Q
  rw [← isReduced_quotient_iff_isRadical]
  let Q' := TensorProduct A (A ⧸ p) B
  let e : Q ≃+* Q' := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).toRingEquiv.trans
    (Algebra.TensorProduct.comm A B (A ⧸ p)).toRingEquiv
  have : Algebra.FormallyUnramified (A ⧸ p) Q' := Algebra.FormallyUnramified.base_change (A ⧸ p)
  have : IsReduced Q' := Algebra.FormallyUnramified.isReduced_of_field (A ⧸ p) Q'
  exact isReduced_of_injective e e.injective

/-- A domain finite and unramified over a Dedekind domain is a Dedekind domain. -/
theorem isDedekindDomain.of_formallyUnramified
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsDedekindDomain A] [IsDomain B] [Algebra.FormallyUnramified A B] : IsDedekindDomain B where
  __ := IsNoetherianRing.of_finite A B
  maximalOfPrime := by
    intro q hq0 hq
    have : (q.under A).IsMaximal := (hq.under A).isMaximal (q.under_ne_bot A hq0)
    exact Ideal.IsMaximal.of_liesOver_isMaximal q (q.under A)
  algebraMap_injective := FaithfulSMul.algebraMap_injective B (FractionRing B)
  isIntegral_iff := by
    have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
    suffices IsIntegrallyClosed B from fun _ ↦ IsIntegrallyClosed.isIntegral_iff
    apply IsIntegrallyClosed.of_localization_maximal
    intro q hq _
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
    let Q := B ⧸ p'
    have : IsArtinianRing Q := IsArtinianRing.of_finite (A ⧸ p) Q
    have h : p'.IsRadical := map_isMaximal_isRadical_of_formallyUnramified A B p
    replace h : p''.IsRadical := by
      rw [← Ideal.radical_eq_iff] at h ⊢
      rw [← IsLocalization.map_radical q.primeCompl, h]
    suffices p''.minimalPrimes = {q'} by
      rw [← h.radical, ← Ideal.sInf_minimalPrimes, this, sInf_singleton]
    rw [Set.eq_singleton_iff_nonempty_unique_mem]
    constructor
    · simp_rw [Set.nonempty_iff_ne_empty, ne_eq, Ideal.minimalPrimes_eq_empty_iff, p'',
        IsLocalization.map_algebraMap_ne_top_iff_disjoint q.primeCompl (Localization.AtPrime q)]
      exact Set.disjoint_compl_left_iff_subset.mpr Ideal.map_comap_le
    · intro r hr
      apply IsLocalRing.eq_maximalIdeal
      apply IsLocalization.isMaximal_of_isMaximal_comap q.primeCompl
      rw [IsLocalization.minimalPrimes_map q.primeCompl, Set.mem_preimage,
        ← Ideal.mk_ker (I := p'), RingHom.ker_eq_comap_bot] at hr
      obtain ⟨s, hs, hs'⟩ := Ideal.exists_minimalPrimes_comap_eq _ _ hr
      replace hs : s.IsPrime := hs.1.1
      replace hs : s.IsMaximal := IsArtinianRing.isMaximal_of_isPrime s
      rw [← hs']
      exact Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk p') Ideal.Quotient.mk_surjective

#lint

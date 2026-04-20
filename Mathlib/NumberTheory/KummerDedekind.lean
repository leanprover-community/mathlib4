/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Paul Lezeau
-/
module

public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.IsAdjoinRoot

/-!
# Kummer-Dedekind theorem

This file proves the Kummer-Dedekind theorem on the splitting of prime ideals in an extension of
the ring of integers. This states the following: assume we are given
  - A prime ideal `I` of Dedekind domain `R`
  - An `R`-algebra `S` that is a Dedekind Domain
  - An `α : S` that is integral over `R` with minimal polynomial `f`

If the conductor `𝓒` of `x` is such that `𝓒 ∩ R` is coprime to `I` then the prime
factorisations of `I * S` and `f mod I` have the same shape, i.e. they have the same number of
prime factors, and each prime factors of `I * S` can be paired with a prime factor of `f mod I` in
a way that ensures multiplicities match (in fact, this pairing can be made explicit
with a formula).

## Main definitions

* `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` : The bijection in the Kummer-Dedekind
  theorem. This is the pairing between the prime factors of `I * S` and the prime factors of
  `f mod I`.

## Main results

* `normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map` : The Kummer-Dedekind
  theorem.
* `Ideal.irreducible_map_of_irreducible_minpoly` : `I.map (algebraMap R S)` is irreducible if
  `(map (Ideal.Quotient.mk I) (minpoly R pb.gen))` is irreducible, where `pb` is a power basis
  of `S` over `R`.
  * `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span` : Let `Q` be a lift of
    factor of the minimal polynomial of `x`, a generator of `S` over `R`, taken
    `mod I`. Then (the reduction of) `Q` corresponds via
    `normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` to
    `span (I.map (algebraMap R S) ∪ {Q.aeval x})`.

## TODO

* Prove the converse of `Ideal.irreducible_map_of_irreducible_minpoly`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

kummer, dedekind, kummer dedekind, dedekind-kummer, dedekind kummer
-/

@[expose] public section


variable {R : Type*} {S : Type*} [CommRing R] [CommRing S] [Algebra R S] {x : S} {I : Ideal R}

open Ideal Polynomial DoubleQuot UniqueFactorizationMonoid Algebra RingHom

namespace KummerDedekind

variable [IsDomain R] [IsIntegrallyClosed R]
variable [IsDedekindDomain S]
variable [Module.IsTorsionFree R S]

attribute [local instance] Ideal.Quotient.field

/--
The isomorphism of rings between `S / I` and `(R / I)[X] / minpoly x` when `I`
and `(conductor R x) ∩ R` are coprime.
-/
noncomputable def quotMapEquivQuotQuotMap (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    S ⧸ I.map (algebraMap R S) ≃+* (R ⧸ I)[X] ⧸ span {(minpoly R x).map (Ideal.Quotient.mk I)} :=
  (quotAdjoinEquivQuotMap hx (FaithfulSMul.algebraMap_injective
    (Algebra.adjoin R {x}) S)).symm.trans <|
    ((Algebra.adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap I).toRingEquiv.trans <|
    quotEquivOfEq (by rw [Algebra.adjoin.powerBasis'_minpoly_gen hx'])

lemma quotMapEquivQuotQuotMap_symm_apply (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) (Q : R[X]) :
    (quotMapEquivQuotQuotMap hx hx').symm (Q.map (Ideal.Quotient.mk I)) = Q.aeval x := by
  apply (quotMapEquivQuotQuotMap hx hx').injective
  rw [quotMapEquivQuotQuotMap, AlgEquiv.toRingEquiv_eq_coe, RingEquiv.symm_trans_apply,
    RingEquiv.symm_symm, RingEquiv.coe_trans, Function.comp_apply, RingEquiv.symm_apply_apply,
    RingEquiv.symm_trans_apply, quotEquivOfEq_symm, quotEquivOfEq_mk]
  congr
  convert (adjoin.powerBasis' hx').quotientEquivQuotientMinpolyMap_symm_apply_mk I Q
  apply (quotAdjoinEquivQuotMap hx
    (FaithfulSMul.algebraMap_injective ((adjoin R {x})) S)).injective
  simp only [RingEquiv.apply_symm_apply, adjoin.powerBasis'_gen, quotAdjoinEquivQuotMap_apply_mk,
    coe_aeval_mk_apply]

open Classical in
/-- The first half of the **Kummer-Dedekind Theorem**, stating that the prime
factors of `I*S` are in bijection with those of the minimal polynomial of the generator of `S`
over `R`, taken `mod I`. -/
noncomputable def normalizedFactorsMapEquivNormalizedFactorsMinPolyMk (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} := by
  refine (normalizedFactorsEquivOfQuotEquiv (quotMapEquivQuotQuotMap hx hx') ?_ ?_).trans ?_
  · rwa [Ne, map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S), ← Ne]
  · by_contra h
    exact (show Polynomial.map (Ideal.Quotient.mk I) (minpoly R x) ≠ 0 from
      Polynomial.map_monic_ne_zero (minpoly.monic hx')) (span_singleton_eq_bot.mp h)
  · refine (normalizedFactorsEquivSpanNormalizedFactors ?_).symm
    exact Polynomial.map_monic_ne_zero (minpoly.monic hx')

open Classical in
/-- The second half of the **Kummer-Dedekind Theorem**, stating that the
bijection `FactorsEquiv'` defined in the first half preserves multiplicities. -/
theorem emultiplicity_factors_map_eq_emultiplicity
    (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) {J : Ideal S}
    (hJ : J ∈ normalizedFactors (I.map (algebraMap R S))) :
    emultiplicity J (I.map (algebraMap R S)) =
      emultiplicity (↑(normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' ⟨J, hJ⟩))
        (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk, Equiv.coe_trans, Function.comp_apply,
    emultiplicity_normalizedFactorsEquivSpanNormalizedFactors_symm_eq_emultiplicity,
    normalizedFactorsEquivOfQuotEquiv_emultiplicity_eq_emultiplicity]

set_option backward.isDefEq.respectTransparency false in
open Classical in
/-- The **Kummer-Dedekind Theorem**. -/
theorem normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map (hI : IsMaximal I)
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    normalizedFactors (I.map (algebraMap R S)) =
      Multiset.map
        (fun f =>
          ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f : Ideal S))
        (normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))).attach := by
  ext J
  -- WLOG, assume J is a normalized factor
  by_cases hJ : J ∈ normalizedFactors (I.map (algebraMap R S))
  swap
  · rw [Multiset.count_eq_zero.mpr hJ, eq_comm, Multiset.count_eq_zero, Multiset.mem_map]
    simp only [not_exists]
    rintro J' ⟨_, rfl⟩
    exact
      hJ ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J').prop
  -- Then we just have to compare the multiplicities, which we already proved are equal.
  have := emultiplicity_factors_map_eq_emultiplicity hI hI' hx hx' hJ
  rw [emultiplicity_eq_count_normalizedFactors, emultiplicity_eq_count_normalizedFactors,
    UniqueFactorizationMonoid.normalize_normalized_factor _ hJ,
    UniqueFactorizationMonoid.normalize_normalized_factor, Nat.cast_inj] at this
  · refine this.trans ?_
    -- Get rid of the `map` by applying the equiv to both sides.
    generalize hJ' :
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx') ⟨J, hJ⟩ = J'
    have : ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm J' : Ideal S) =
        J := by
      rw [← hJ', Equiv.symm_apply_apply _ _, Subtype.coe_mk]
    subst this
    -- Get rid of the `attach` by applying the subtype `coe` to both sides.
    rw [Multiset.count_map_eq_count' fun f =>
        ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm f :
          Ideal S),
      Multiset.count_attach]
    · exact Subtype.coe_injective.comp (Equiv.injective _)
  · exact (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact irreducible_of_normalized_factor _
        (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx' _).prop
  · exact Polynomial.map_monic_ne_zero (minpoly.monic hx')
  · exact irreducible_of_normalized_factor _ hJ
  · rwa [← bot_eq_zero, Ne,
      map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)]

set_option backward.isDefEq.respectTransparency false in
theorem Ideal.irreducible_map_of_irreducible_minpoly (hI : IsMaximal I) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x)
    (hf : Irreducible (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))) :
    Irreducible (I.map (algebraMap R S)) := by
  classical
  have mem_norm_factors : normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) ∈
      normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)) := by
    simp [normalizedFactors_irreducible hf]
  suffices ∃ y, normalizedFactors (I.map (algebraMap R S)) = {y} by
    obtain ⟨y, hy⟩ := this
    have h := prod_normalizedFactors (show I.map (algebraMap R S) ≠ 0 by
          rwa [← bot_eq_zero, Ne,
            map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R S)])
    rw [associated_iff_eq, hy, Multiset.prod_singleton] at h
    rw [← h]
    exact
      irreducible_of_normalized_factor y
        (show y ∈ normalizedFactors (I.map (algebraMap R S)) by simp [hy])
  rw [normalizedFactors_ideal_map_eq_normalizedFactors_min_poly_mk_map hI hI' hx hx']
  use ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm
        ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩ :
      Ideal S)
  rw [Multiset.map_eq_singleton]
  use ⟨normalize (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x)), mem_norm_factors⟩
  refine ⟨?_, rfl⟩
  apply Multiset.map_injective Subtype.coe_injective
  rw [Multiset.attach_map_val, Multiset.map_singleton, Subtype.coe_mk]
  exact normalizedFactors_irreducible hf

set_option backward.isDefEq.respectTransparency false in
open Set Classical in
/-- Let `Q` be a lift of factor of the minimal polynomial of `x`, a generator of `S` over `R`, taken
`mod I`. Then (the reduction of) `Q` corresponds via
`normalizedFactorsMapEquivNormalizedFactorsMinPolyMk` to
`span (I.map (algebraMap R S) ∪ {Q.aeval x})`. -/
theorem normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span
    (hI : I.IsMaximal) {Q : R[X]}
    (hQ : Q.map (Ideal.Quotient.mk I) ∈ normalizedFactors ((minpoly R x).map (Ideal.Quotient.mk I)))
    (hI' : I ≠ ⊥) (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤) (hx' : IsIntegral R x) :
    ((normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx').symm ⟨_, hQ⟩).val =
    span (I.map (algebraMap R S) ∪ {Q.aeval x}) := by
  dsimp [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk,
    normalizedFactorsEquivSpanNormalizedFactors]
  rw [normalizedFactorsEquivOfQuotEquiv_symm]
  dsimp [normalizedFactorsEquivOfQuotEquiv, idealFactorsEquivOfQuotEquiv, OrderIso.ofHomInv]
  simp only [map_span, image_singleton, coe_coe, quotMapEquivQuotQuotMap_symm_apply hx hx' Q]
  refine le_antisymm (fun a ha ↦ ?_) (span_le.mpr <| union_subset_iff.mpr <|
    ⟨le_comap_of_map_le (by simp), by simp [mem_span_singleton]⟩)
  rw [mem_comap, Ideal.mem_span_singleton] at ha
  obtain ⟨a', ha'⟩ := ha
  obtain ⟨b, hb⟩ := Ideal.Quotient.mk_surjective a'
  rw [← hb, ← map_mul, Quotient.mk_eq_mk_iff_sub_mem] at ha'
  rw [union_comm, span_union, span_eq, mem_span_singleton_sup]
  exact ⟨b, a - Q.aeval x * b, ha', by ring⟩

end KummerDedekind

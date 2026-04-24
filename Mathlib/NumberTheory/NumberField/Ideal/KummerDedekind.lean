/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.KummerDedekind
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.RamificationInertia.Basic
public import Mathlib.RingTheory.Ideal.Int

/-!
# Kummer-Dedekind criterion for the splitting of prime numbers

In this file, we give a specialized version of the Kummer-Dedekind criterion for the case of the
splitting of rational primes in number fields.

## Main definitions

Let `K` be a number field and `θ` an algebraic integer of `K`.

* `RingOfIntegers.exponent`: the smallest positive integer `d` contained in the conductor of `θ`.
  It is the smallest integer such that `d • 𝓞 K ⊆ ℤ[θ]`, see `RingOfIntegers.exponent_eq_sInf`.

* `RingOfIntegers.ZModXQuotSpanEquivQuotSpan`: The isomorphism between `(ℤ / pℤ)[X] / (minpoly θ)`
  and `𝓞 K / p(𝓞 K)` for a prime `p` which doesn't divide the exponent of `θ`.

* `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`: The bijection between the prime ideals
  of `K` above `p` and the monic irreducible factors of `minpoly ℤ θ` modulo `p` for a prime `p`
  which doesn't divide the exponent of `θ`.

## Main results

* `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod`: The ideal corresponding to the class
  of `Q ∈ ℤ[X]` modulo `p` via `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is spanned
  by `p` and `Q(θ)`.

* `NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply`: The residual degree
  of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the degree of `Q mod p`.

* `NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply`: The
  ramification index of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
  `NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the multiplicity of `Q mod p`
  in `minpoly ℤ θ`.

-/

@[expose] public section

noncomputable section

open Polynomial NumberField Ideal KummerDedekind UniqueFactorizationMonoid

variable {K : Type*} [Field K]

namespace RingOfIntegers

/--
The smallest positive integer `d` contained in the conductor of `θ`. It is the smallest integer
such that `d • 𝓞 K ⊆ ℤ[θ]`, see `exponent_eq_sInf`. It is set to `0` if `d` does not exists.
-/
def exponent (θ : 𝓞 K) : ℕ := absNorm (under ℤ (conductor ℤ θ))

variable {θ : 𝓞 K}

theorem exponent_eq_one_iff : exponent θ = 1 ↔ Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [exponent, absNorm_eq_one_iff, comap_eq_top_iff, conductor_eq_top_iff_adjoin_eq_top]

theorem not_dvd_exponent_iff {p : ℕ} [Fact (Nat.Prime p)] :
    ¬ p ∣ exponent θ ↔ Codisjoint (comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ)) (span {↑p}) := by
  rw [codisjoint_comm, ← IsCoatom.not_le_iff_codisjoint, ← under_def, ← Ideal.dvd_iff_le,
    ← Int.ideal_span_absNorm_eq_self (under ℤ (conductor ℤ θ)),
    Ideal.span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
  exact isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p

theorem exponent_eq_sInf : exponent θ = sInf {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ} := by
  rw [exponent, Int.absNorm_under_eq_sInf]

variable [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact p.Prime]

/--
If `p` doesn't divide the exponent of `θ`, then `(ℤ / pℤ)[X] / (minpoly θ) ≃+* 𝓞 K / p(𝓞 K)`.
-/
def ZModXQuotSpanEquivQuotSpan (hp : ¬ p ∣ exponent θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (by simp [Ideal.map_span, Polynomial.map_map])).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))

theorem ZModXQuotSpanEquivQuotSpan_mk_apply (hp : ¬ p ∣ exponent θ) (Q : ℤ[X]) :
    (ZModXQuotSpanEquivQuotSpan hp)
      (Ideal.Quotient.mk (span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})
      (map (Int.castRingHom (ZMod p)) Q)) = Ideal.Quotient.mk (span {(p : 𝓞 K)}) (aeval θ Q) := by
  simp only [ZModXQuotSpanEquivQuotSpan, algebraMap_int_eq,
    RingEquiv.trans_apply, AlgEquiv.coe_ringEquiv, quotientEquivAlgOfEq_mk,
    quotientEquiv_symm_apply, quotientMap_mk, RingHom.coe_coe, mapEquiv_symm_apply,
    Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom]
  exact congr_arg (quotientEquivAlgOfEq ℤ (by simp [map_span])) <|
    quotMapEquivQuotQuotMap_symm_apply (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral Q

variable (p θ) in
/--
The finite set of monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
abbrev monicFactorsMod : Finset ((ZMod p)[X]) :=
  (normalizedFactors (map (Int.castRingHom (ZMod p)) (minpoly ℤ θ))).toFinset

/--
If `p` does not divide `exponent θ` and `Q` is a lift of a monic irreducible factor of
`minpoly ℤ θ` modulo `p`, then `(ℤ / pℤ)[X] / Q ≃+* 𝓞 K / (p, Q(θ))`.
-/
def ZModXQuotSpanEquivQuotSpanPair (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    (ZMod p)[X] ⧸ span {Polynomial.map (Int.castRingHom (ZMod p)) Q} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K), (aeval θ) Q} :=
  have h₀ : map (Int.castRingHom (ZMod p)) (minpoly ℤ θ) ≠ 0 :=
      map_monic_ne_zero (minpoly.monic θ.isIntegral)
  have h_eq₁ : span {map (Int.castRingHom (ZMod p)) Q} =
      span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ⊔
        span {map (Int.castRingHom (ZMod p)) Q} := by
    rw [← span_insert, span_pair_comm, span_pair_eq_span_left_iff_dvd.mpr]
    simp only [Multiset.mem_toFinset] at hQ
    exact ((Polynomial.mem_normalizedFactors_iff h₀).mp hQ).2.2
  have h_eq₂ : span {↑p} ⊔ span {(aeval θ) Q} = span {↑p, (aeval θ) Q} := by
    rw [span_insert]
  ((Ideal.quotEquivOfEq h_eq₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv
      (Ideal.map (Ideal.Quotient.mk _) (span {(Polynomial.map (Int.castRingHom (ZMod p)) Q)}))
      (Ideal.map (Ideal.Quotient.mk _) (span {aeval θ Q})) (ZModXQuotSpanEquivQuotSpan hp) (by
        simp [map_span, ZModXQuotSpanEquivQuotSpan_mk_apply])).trans <|
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq h_eq₂)

end RingOfIntegers

open RingOfIntegers IsDedekindDomain
namespace NumberField.Ideal

variable {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

set_option backward.privateInPublic true in
open scoped Classical in
private def primesOverSpanEquivMonicFactorsModAux (A : ℤ[X]) :
    {Q // Q ∈ normalizedFactors (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)} ≃
    (normalizedFactors (map (Int.castRingHom (ZMod p)) A)).toFinset :=
  (normalizedFactorsEquiv (f := (mapEquiv (Int.quotientSpanNatEquivZMod p)).toMulEquiv)
    (by simp) (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)).trans
      (Equiv.subtypeEquivRight (fun _ ↦ by simp [Polynomial.map_map]))

private theorem primesOverSpanEquivMonicFactorsModAux_symm_apply (A : ℤ[X]) {Q : (ZMod p)[X]}
    (hQ : Q ∈ (normalizedFactors (map (Int.castRingHom (ZMod p)) A)).toFinset) :
    ((primesOverSpanEquivMonicFactorsModAux A).symm ⟨Q, hQ⟩ : (ℤ ⧸ span {(p : ℤ)})[X]) =
      Polynomial.map ((Int.quotientSpanNatEquivZMod p).symm) Q := rfl

variable [NumberField K]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/--
If `p` does not divide `exponent θ`, then the prime ideals above `p` in `K` are in bijection
with the monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
def primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod θ p :=
  have h : span {(p : ℤ)} ≠ ⊥ := by simp [NeZero.ne p]
  ((Equiv.setCongr (by ext; simp [mem_primesOver_iff_mem_normalizedFactors _ h])).trans
    (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (Int.ideal_span_isMaximal_of_prime p) h
      (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral)).trans <|
        (primesOverSpanEquivMonicFactorsModAux _)

theorem primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        inferInstance (by simp [NeZero.ne p]) (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral).symm
        ⟨Q.map (Int.quotientSpanNatEquivZMod p).symm, by
          rw [← primesOverSpanEquivMonicFactorsModAux_symm_apply]
          exact ((primesOverSpanEquivMonicFactorsModAux _).symm ⟨Q, hQ⟩).coe_prop⟩ := rfl

/--
The ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is spanned by `p` and `Q(θ)`.
-/
theorem primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  simp only [primesOverSpanEquivMonicFactorsMod_symm_apply, Polynomial.map_map,
    Int.quotientSpanNatEquivZMod_comp_castRingHom]
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span,
    span_union, span_eq, map_span, Set.image_singleton, map_natCast, ← span_insert]

theorem liesOver_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    LiesOver (span {(p : (𝓞 K)), aeval θ Q}) (span {(p : ℤ)}) := by
  rw [← Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ]
  exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).prop.2

/--
The residual degree of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the degree of `Q mod p`.
-/
theorem inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)}) ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        natDegree (Q.map (Int.castRingHom (ZMod p))) := by
  -- This is needed for `inertiaDeg_algebraMap` below to work
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span, inertiaDeg_algebraMap,
    ← finrank_quotient_span_eq_natDegree]
  refine Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod p) ?_ (by ext; simp)
  exact (ZModXQuotSpanEquivQuotSpanPair hp hQ).symm

theorem inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) = natDegree Q := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply]

/--
The ramification index of the ideal corresponding to the class of `Q ∈ ℤ[X]` modulo `p` via
`NumberField.Ideal.primesOverSpanEquivMonicFactorsMod` is equal to the multiplicity of `Q mod p` in
`minpoly ℤ θ`.
-/
theorem ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    ramificationIdx (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
          multiplicity (Q.map (Int.castRingHom (ZMod p)))
            ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  rw [ramificationIdx_eq_multiplicity (map_ne_bot_of_ne_bot (by simp [NeZero.ne p])) inferInstance]
  · apply multiplicity_eq_of_emultiplicity_eq
    rw [← emultiplicity_map_eq (mapEquiv (Int.quotientSpanNatEquivZMod p).symm),
      emultiplicity_factors_map_eq_emultiplicity inferInstance (by simp [NeZero.ne p])
      (not_dvd_exponent_iff.mp hp).eq_top θ.isIntegral]
    · simp only [primesOverSpanEquivMonicFactorsMod_symm_apply,
        Equiv.apply_symm_apply (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk _ _ _ _),
        Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_castRingHom, mapEquiv_apply]
    · rw [← mem_primesOver_iff_mem_normalizedFactors _ (by simp [NeZero.ne p])]
      exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).coe_prop

theorem ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    ramificationIdx (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply]

end NumberField.Ideal

/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Int

/-!
# Kummer-Dedekind criterion for the splitting of prime numbers

In this file, we give a specialized version of the Kummer-Dedekind criterion for the case of the
splitting of rational primes in number fields.

## Main definitions

* TODO

## Main results

* TODO

-/

noncomputable section

open Polynomial NumberField Ideal KummerDedekind UniqueFactorizationMonoid

variable {K : Type*} [Field K]

namespace RingOfIntegers

/--
The smallest positive integer `d` such that `d • 𝓞 K ⊆ ℤ[θ]`, see `exponent_eq_sInf`. It is equal
to `0` if `d` does not exists.
-/
def exponent (θ : 𝓞 K) : ℕ := absNorm (under ℤ (conductor ℤ θ))

variable {θ : 𝓞 K}

theorem exponent_eq_one_iff :
    exponent θ = 1 ↔ Algebra.adjoin ℤ {θ} = ⊤ := by
  rw [exponent, absNorm_eq_one_iff, comap_eq_top_iff, conductor_eq_top_iff_adjoin_eq_top]

theorem not_dvd_exponent_iff {p : ℕ} [Fact (Nat.Prime p)] :
    ¬ p ∣ exponent θ ↔ comap (algebraMap ℤ (𝓞 K)) (conductor ℤ θ) ⊔ span {(p : ℤ)} = ⊤ := by
  rw [sup_comm, IsCoatom.sup_eq_top_iff, ← under_def, ← Ideal.dvd_iff_le,
    Int.ideal_eq_span_absNorm_self (under ℤ (conductor ℤ θ)),
    span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
  exact isMaximal_def.mp <| Int.ideal_span_isMaximal_of_prime p

theorem exponent_eq_sInf :
    exponent θ = sInf {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ} := by
  rw [exponent, Int.absNorm_under_eq_sInf]

variable [NumberField K] {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

/--
If `p` doesn't divide the exponent of `θ`, then `(ℤ / pℤ)[X] / (minpoly θ) ≃+* 𝓞 K / p(𝓞 K)`.
-/
def ZModXQuotSpanEquivQuotSpan (hp : ¬ p ∣ exponent θ) :
    (ZMod p)[X] ⧸ span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)} ≃+*
      𝓞 K ⧸ span {(p : 𝓞 K)} :=
  (quotientEquivAlgOfEq ℤ (by simp [Ideal.map_span, Polynomial.map_map])).toRingEquiv.trans
    ((quotientEquiv _ _ (mapEquiv (Int.quotientSpanNatEquivZMod p)) rfl).symm.trans
      ((quotMapEquivQuotQuotMap (not_dvd_exponent_iff.mp hp) θ.isIntegral).symm.trans
        (quotientEquivAlgOfEq ℤ (by simp [map_span])).toRingEquiv))

theorem ZModXQuotSpanEquivQuotSpan_mk_apply (hp : ¬ p ∣ exponent θ) (Q : ℤ[X]) :
  (ZModXQuotSpanEquivQuotSpan hp)
    (Ideal.Quotient.mk (span {map (Int.castRingHom (ZMod p)) (minpoly ℤ θ)})
      (map (Int.castRingHom (ZMod p)) Q)) = Ideal.Quotient.mk (span {(p : 𝓞 K)}) (aeval θ Q) := by
  unfold ZModXQuotSpanEquivQuotSpan
  simp only [AlgEquiv.toRingEquiv_eq_coe, algebraMap_int_eq, RingEquiv.trans_apply,
    AlgEquiv.coe_ringEquiv, quotientEquivAlgOfEq_mk, quotientEquiv_symm_apply, quotientMap_mk,
    RingHom.coe_coe, mapEquiv_symm_apply, Polynomial.map_map,
    Int.quotientSpanNatEquivZMod_comp_castRingHom]
  exact congr_arg (quotientEquivAlgOfEq ℤ (by simp [map_span])) <|
    quotMapEquivQuotQuotMap_symm_apply (not_dvd_exponent_iff.mp hp) θ.isIntegral Q

variable (p θ) in
/--
The set of monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
abbrev monicFactorsMod : Set ((ZMod p)[X]) :=
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
    rw [← span_insert, span_pair_comm, span_pair_eq_span_singleton_iff_dvd.mpr]
    simp only [Finset.mem_coe, Multiset.mem_toFinset] at hQ
    exact ((Polynomial.mem_normalizedFactors_iff h₀).mp hQ).2.2
  have h_eq₂ : span {↑p} ⊔ span {(aeval θ) Q} = span {↑p, (aeval θ) Q} := by
    rw [span_insert]
  ((Ideal.quotEquivOfEq h_eq₁).trans (DoubleQuot.quotQuotEquivQuotSup _ _).symm).trans <|
    (Ideal.quotientEquiv
      (Ideal.map (Ideal.Quotient.mk _) (span {(Polynomial.map (Int.castRingHom (ZMod p)) Q)}))
      (Ideal.map (Ideal.Quotient.mk _) (span {aeval θ Q})) (ZModXQuotSpanEquivQuotSpan hp) (by
        simp [Ideal.map_map, map_span, ZModXQuotSpanEquivQuotSpan_mk_apply])).trans <|
    (DoubleQuot.quotQuotEquivQuotSup _ _).trans (Ideal.quotEquivOfEq h_eq₂)

end RingOfIntegers

open RingOfIntegers IsDedekindDomain
namespace NumberField

variable {θ : 𝓞 K} {p : ℕ} [Fact (Nat.Prime p)]

attribute [local instance] Int.ideal_span_isMaximal_of_prime Ideal.Quotient.field

open scoped Classical in
private def Ideal.primesOverSpanEquivMonicFactorsModAux (A : ℤ[X]) :
    {Q | Q ∈ normalizedFactors (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)} ≃
    (normalizedFactors (map (Int.castRingHom (ZMod p)) A)).toFinset :=
  (normalizedFactorsEquiv (f := (mapEquiv (Int.quotientSpanNatEquivZMod p)).toMulEquiv)
    (by simp) (map (Ideal.Quotient.mk (span {(p : ℤ)})) A)).trans
      (Equiv.setCongr (by
        classical
        ext
        simp_rw [RingEquiv.toMulEquiv_eq_coe, RingEquiv.coe_toMulEquiv, mapEquiv_apply,
          Set.mem_setOf_eq, Multiset.toFinset_val, Set.mem_def, Multiset.mem_dedup,
          Polynomial.map_map, Int.quotientSpanNatEquivZMod_comp_Quotient_mk]))

private theorem Ideal.primesOverSpanEquivMonicFactorsModAux_symm_apply (A : ℤ[X]) {Q : (ZMod p)[X]}
    (hQ : Q ∈ (normalizedFactors (map (Int.castRingHom (ZMod p)) A)).toFinset) :
    ((Ideal.primesOverSpanEquivMonicFactorsModAux A).symm ⟨Q, hQ⟩ : (ℤ ⧸ span {(p : ℤ)})[X]) =
      Polynomial.map ((Int.quotientSpanNatEquivZMod p).symm) Q := rfl

variable [NumberField K]

open scoped Classical in
/--
If `p` does not divide `exponent θ`, then the prime ideals above `p` in `K` are in bijection
with the monic irreducible factors of `minpoly ℤ θ` modulo `p`.
-/
def Ideal.primesOverSpanEquivMonicFactorsMod (hp : ¬ p ∣ exponent θ) :
    primesOver (span {(p : ℤ)}) (𝓞 K) ≃ monicFactorsMod θ p :=
  have h : span {(p : ℤ)} ≠ ⊥ := by simp [NeZero.ne p]
  ((Equiv.setCongr (by ext; simp [mem_primesOver_iff_mem_normalizedFactors _ h])).trans
    (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
    (Int.ideal_span_isMaximal_of_prime p) h (not_dvd_exponent_iff.mp hp) θ.isIntegral)).trans <|
      (Ideal.primesOverSpanEquivMonicFactorsModAux _)

theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    ((Ideal.primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
      (normalizedFactorsMapEquivNormalizedFactorsMinPolyMk
        inferInstance (by simp [NeZero.ne p]) (not_dvd_exponent_iff.mp hp) θ.isIntegral).symm
        ⟨Q.map (Int.quotientSpanNatEquivZMod p).symm, by
          rw [← Ideal.primesOverSpanEquivMonicFactorsModAux_symm_apply]
          exact ((Ideal.primesOverSpanEquivMonicFactorsModAux _).symm ⟨Q, hQ⟩).coe_prop⟩ := rfl

theorem Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    (hp : ¬ p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        span {(p : (𝓞 K)), aeval θ Q} := by
  simp only [primesOverSpanEquivMonicFactorsMod_symm_apply, Polynomial.map_map,
    Int.quotientSpanNatEquivZMod_comp_castRingHom]
  rw [normalizedFactorsMapEquivNormalizedFactorsMinPolyMk_symm_apply_eq_span,
    span_union, span_eq, map_span, Set.image_singleton, map_natCast, ← span_insert]

theorem Ideal.liesOver_primesOverSpanEquivMonicFactorsMod_symm (hp : ¬ ↑p ∣ exponent θ) {Q : ℤ[X]}
    (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    LiesOver (span {(p : (𝓞 K)), aeval θ Q}) (span {(p : ℤ)}) := by
  rw [← Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span hp hQ]
  exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).prop.2

theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)}) ((primesOverSpanEquivMonicFactorsMod hp).symm
      ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
        natDegree (Q.map (Int.castRingHom (ZMod p))) := by
  -- Register this instance for `inertiaDeg_algebraMap` below
  have := liesOver_primesOverSpanEquivMonicFactorsMod_symm hp hQ
  have hQ' : Polynomial.map (Int.castRingHom (ZMod p)) Q ≠ 0 := by
    contrapose! hQ
    rw [hQ]
    simp only [Finset.mem_coe, Multiset.mem_toFinset]
    exact zero_not_mem_normalizedFactors _
  rw [primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span, inertiaDeg_algebraMap,
    ← finrank_quotient_span_eq_natDegree hQ']
  refine Algebra.finrank_eq_of_equiv_equiv (Int.quotientSpanNatEquivZMod p) ?_ ?_
  · exact (ZModXQuotSpanEquivQuotSpanPair hp hQ).symm
  · ext; simp

theorem Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    inertiaDeg (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        natDegree Q := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply]

theorem Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply (hp : ¬ p ∣ exponent θ)
    {Q : ℤ[X]} (hQ : Q.map (Int.castRingHom (ZMod p)) ∈ monicFactorsMod θ p) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm
        ⟨Q.map (Int.castRingHom (ZMod p)), hQ⟩ : Ideal (𝓞 K)) =
          multiplicity (Q.map (Int.castRingHom (ZMod p)))
            ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  have h : span {(p : ℤ)} ≠ ⊥ := by simp [NeZero.ne p]
  rw [ramificationIdx_eq_multiplicity (RingHom.injective_int _) (by simp [NeZero.ne p])
    inferInstance]
  · apply multiplicity_eq_of_emultiplicity_eq
    rw [← emultiplicity_map_eq (mapEquiv (Int.quotientSpanNatEquivZMod p).symm),
      emultiplicity_factors_map_eq_emultiplicity inferInstance (by simp [NeZero.ne p])
      (not_dvd_exponent_iff.mp hp) θ.isIntegral]
    · simp_rw [primesOverSpanEquivMonicFactorsMod_symm_apply]
      rw [Equiv.apply_symm_apply]
      simp [Polynomial.map_map]
    · rw [← mem_primesOver_iff_mem_normalizedFactors _ h]
      exact ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).coe_prop
  · have := ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨_, hQ⟩).prop.2
    exact Ideal.ne_bot_of_liesOver_of_ne_bot h _

theorem Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' (hp : ¬ p ∣ exponent θ)
    {Q : (ZMod p)[X]} (hQ : Q ∈ monicFactorsMod θ p) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) (span {(p : ℤ)})
      ((primesOverSpanEquivMonicFactorsMod hp).symm ⟨Q, hQ⟩ : Ideal (𝓞 K)) =
        multiplicity Q ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))) := by
  obtain ⟨S, rfl⟩ := (map_surjective _ (ZMod.ringHom_surjective (Int.castRingHom (ZMod p)))) Q
  rw [ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply]

end NumberField

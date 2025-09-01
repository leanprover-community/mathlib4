/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.KummerDedekind
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Int

/-!
# Kummer-Dedekind criterion for the splitting of prime numbers

In this file, we give a specialized version of the Kummer-Dedekind criterion for the case of the
splitting of rational primes in number fields.

## Main definitions

* `RingOfIntegers.exponent`: the smallest positive integer `d` contained in the conductor of `θ`.
  It is the smallest integer such that `d • 𝓞 K ⊆ ℤ[θ]`, see `RingOfIntegers.exponent_eq_sInf`.

* `RingOfIntegers.ZModXQuotSpanEquivQuotSpan`: The isomorphism between `(ℤ / pℤ)[X] / (minpoly θ)`
  and `𝓞 K / p(𝓞 K)` for a prime `p` which doesn't divide the exponent of `θ`.

-/

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
    span_singleton_dvd_span_singleton_iff_dvd, Int.natCast_dvd_natCast, exponent]
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
  simp only [ZModXQuotSpanEquivQuotSpan, AlgEquiv.toRingEquiv_eq_coe, algebraMap_int_eq,
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

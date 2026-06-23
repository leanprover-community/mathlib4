/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits

/-!
# Ideals in cyclotomic fields

In this file, we prove results about ideals in cyclotomic extensions of `ℚ`.

## Main results

* `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`: there is only one prime ideal above
  the prime `p` in `ℚ(ζ_pᵏ)`

* `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow`: the residual degree of the prime ideal
  above `p` in `ℚ(ζ_pᵏ)` is `1`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_prime_pow`: the ramification index of the prime
  ideal above `p` in `ℚ(ζ_pᵏ)` is `p ^ (k - 1) * (p - 1)`.

* `IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd`: if the prime `p` does not divide `m`, then
  the inertia degree of `p` in `ℚ(ζₘ)` is the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd`: if the prime `p` does not divide `m`,
  then the ramification index of `p` in `ℚ(ζₘ)` is `1`.

* `IsCyclotomicExtension.Rat.inertiaDegIn_eq`: write `n = p ^ (k + 1) * m` where the prime `p` does
  not divide `m`, then the inertia degree of `p` in `ℚ(ζₙ)` is the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdxIn_eq`: write `n = p ^ (k + 1) * m` where the prime `p`
  does not divide `m`, then the ramification index of `p` in `ℚ(ζₙ)` is `p ^ k * (p - 1)`.

-/

public section

namespace IsCyclotomicExtension.Rat

open Ideal NumberField RingOfIntegers

variable (n m p k : ℕ) [hp : Fact (Nat.Prime p)] (K : Type*) [Field K] [NumberField K]
  (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver (span {(p : ℤ)})]

local notation3 "𝒑" => (span {(p : ℤ)})

section PrimePow

variable {K} [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

instance isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1}) := by
  rw [span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

theorem associated_norm_zeta_sub_one : Associated (Algebra.norm ℤ (hζ.toInteger - 1)) (p : ℤ) := by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h, zero_add, pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two, h, Int.ofNat_two, Associated.neg_left_iff]
    | succ n =>
      rw [h, add_assoc, one_add_one_eq_two] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two_pow, h, Int.ofNat_two]
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two h]

theorem absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p := by
  simpa using congr_arg absNorm <|
    span_singleton_eq_span_singleton.mpr <| associated_norm_zeta_sub_one p k hζ

theorem p_mem_span_zeta_sub_one : (p : 𝓞 K) ∈ span {hζ.toInteger - 1} := by
  convert! absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

theorem span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

instance liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑 := by
  rw [liesOver_iff]
  refine IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

theorem inertiaDeg_span_zeta_sub_one : inertiaDeg' (span {hζ.toInteger - 1}) ℤ = 1 := by
  have : IsMaximal (span {hζ.toInteger - 1}) := .of_liesOver_isMaximal _ 𝒑
  rw [← inertiaDeg_eq_inertiaDeg' 𝒑]
  rw [← Nat.pow_right_inj hp.out.one_lt, pow_one, ← absNorm_eq_pow_inertiaDeg' _ hp.out,
    absNorm_span_zeta_sub_one]

attribute [local instance] FractionRing.liftAlgebra in
theorem map_eq_span_zeta_sub_one_pow :
    (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : IsGalois (FractionRing ℤ) (FractionRing (𝓞 K)) := by
    refine IsGalois.of_equiv_equiv (f := (FractionRing.algEquiv ℤ ℚ).toRingEquiv.symm)
      (g := (FractionRing.algEquiv (𝓞 K) K).toRingEquiv.symm) <|
        RingHom.ext fun x ↦ IsFractionRing.algEquiv_commutes (FractionRing.algEquiv ℤ ℚ).symm
          (FractionRing.algEquiv (𝓞 K) K).symm _
  rw [map_span, Set.image_singleton, span_singleton_eq_span_singleton.mpr
    ((associated_norm_zeta_sub_one p k hζ).symm.map (algebraMap ℤ (𝓞 K))),
    ← Algebra.intNorm_eq_norm, Algebra.algebraMap_intNorm_of_isGalois, ← prod_span_singleton]
  conv_lhs =>
    enter [2, σ]
    rw [span_singleton_eq_span_singleton.mpr
      (hζ.toInteger_isPrimitiveRoot.associated_sub_one_map_sub_one σ).symm]
  rw [Finset.prod_const, Finset.card_univ, ← Fintype.card_congr (galRestrict ℤ ℚ K (𝓞 K)).toEquiv,
    ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]

theorem ramificationIdx_span_zeta_sub_one :
    ramificationIdx' (span {hζ.toInteger - 1}) ℤ = p ^ k * (p - 1) := by
  have h := isPrime_span_zeta_sub_one p k hζ
  have hp0 : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  rw [← ramificationIdx_eq_ramificationIdx' 𝒑 _ hp0,
    ← Nat.totient_prime_pow_succ hp.out, ← finrank _ K,
    IsDedekindDomain.ramificationIdx_eq_multiplicity _ h, map_eq_span_zeta_sub_one_pow p k hζ,
    multiplicity_pow_self (span_zeta_sub_one_ne_bot p k hζ) (isUnit_iff.not.mpr h.ne_top)]
  exact map_ne_bot_of_ne_bot hp0

variable (K)

include hK in
theorem ncard_primesOver_of_prime_pow :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/ℚ)
  have hζ := hK.zeta_spec
  have := liesOver_span_zeta_sub_one p k hζ
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) Gal(K/ℚ),
    inertiaDegIn_eq_inertiaDeg 𝒑 (span {hζ.toInteger - 1}) Gal(K/ℚ),
    inertiaDeg_span_zeta_sub_one,
    ramificationIdx_span_zeta_sub_one, mul_one, ← Nat.totient_prime_pow_succ hp.out,
    ← finrank _ K, IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, Nat.mul_eq_right] at h_main
  exact Module.finrank_pos.ne'

theorem eq_span_zeta_sub_one_of_liesOver (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  have : P ∈ primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} ∈ primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in
theorem inertiaDeg_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg' P ℤ = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one]

include hK in
theorem ramificationIdx_eq_of_prime_pow (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx' P ℤ = p ^ k * (p - 1) := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one]

include hK in
theorem inertiaDegIn_eq_of_prime_pow :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/ℚ),
    inertiaDeg_span_zeta_sub_one]

include hK in
theorem ramificationIdxIn_eq_of_prime_pow :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hK.zeta_spec.toInteger - 1}) Gal(K/ℚ),
    ramificationIdx_span_zeta_sub_one]

end PrimePow

section Prime

variable {K} [hK : IsCyclotomicExtension {p} ℚ K] {ζ : K} (hζ : IsPrimitiveRoot ζ p)

instance isPrime_span_zeta_sub_one' : IsPrime (span {hζ.toInteger - 1}) := by
  rw [← pow_one p] at hK hζ
  exact isPrime_span_zeta_sub_one p 0 hζ

/-- If `2 < p`, then `2` is not in the ideal `(ζ - 1)`, where `ζ` is a primitive `p`-th root of
unity. -/
theorem two_not_mem_span_zeta_sub_one' (h : 2 < p) : (2 : 𝓞 K) ∉ span {hζ.toInteger - 1} := by
  rw [mem_span_singleton]
  rw [← pow_one p] at hK hζ
  exact hζ.toInteger_sub_one_not_dvd_two h.ne'

omit hp hK [NumberField K] in
lemma associated_sub_one_of_isPrimitiveRoot [NeZero p] {η : K} (hη : IsPrimitiveRoot η p) :
    Associated (hζ.toInteger - 1) (hη.toInteger - 1) := by
  obtain ⟨i, -, hi, hζη⟩ := hζ.isPrimitiveRoot_iff.mp hη
  rw [show hη.toInteger = hζ.toInteger ^ i from RingOfIntegers.ext hζη.symm]
  exact hζ.toInteger_isPrimitiveRoot.associated_sub_one_pow_sub_one_of_coprime hi

@[deprecated "The statement has been changed to use the `ζ - 1` spelling rather than `1 - ζ`, \
for consistency with the rest of the API, so the type is now different. \
Use `associated_sub_one_of_isPrimitiveRoot` instead." (since := "2026-06-23")]
alias associated_one_sub_of_isPrimitiveRoot := associated_sub_one_of_isPrimitiveRoot

omit [NumberField K] hK in
open Polynomial in
/-- `(ζ - 1) ^ (p - 1)` is associated to `p`, where `ζ` is a primitive `p`-th root of unity and
`p` is prime. -/
theorem associated_zeta_sub_one_pow_prime :
    Associated ((hζ.toInteger - 1) ^ (p - 1)) (p : 𝓞 K) := by
  rw [← eval_one_cyclotomic_prime (R := 𝓞 K) (p := p),
    cyclotomic_eq_prod_X_sub_primitiveRoots hζ.toInteger_isPrimitiveRoot, eval_prod]
  simp only [eval_sub, eval_X, eval_C]
  rw [← Nat.totient_prime hp.out, ← hζ.toInteger_isPrimitiveRoot.card_primitiveRoots,
    ← Finset.prod_const]
  refine Associated.prod _ _ _ fun η hη ↦ ?_
  have hη' : IsPrimitiveRoot (η : K) p :=
    (isPrimitiveRoot_of_mem_primitiveRoots hη).map_of_injective RingOfIntegers.coe_injective
  simpa using (associated_sub_one_of_isPrimitiveRoot p hζ hη').neg_right

/-- If `ζ - 1` does not divide `x`, then `p` and `x` are coprime, where `ζ` is a primitive `p`-th
root of unity and `p` is prime. -/
theorem isCoprime_of_not_zeta_sub_one_dvd {x : 𝓞 K} (hx : ¬ hζ.toInteger - 1 ∣ x) :
    IsCoprime (p : 𝓞 K) x := by
  rwa [← isCoprime_span_singleton_iff,  ← span_singleton_eq_span_singleton.mpr
    (associated_zeta_sub_one_pow_prime p hζ), ← span_singleton_pow,
    IsCoprime.pow_left_iff (by grind [hp.out.one_lt]), isCoprime_iff_gcd,
    (prime_span_singleton_iff.mpr
    hζ.zeta_sub_one_prime').irreducible.gcd_eq_one_iff, dvd_span_singleton, mem_span_singleton]

theorem inertiaDeg_span_zeta_sub_one' : inertiaDeg' (span {hζ.toInteger - 1}) ℤ = 1 := by
  rw [← pow_one p] at hK hζ
  exact inertiaDeg_span_zeta_sub_one p 0 hζ

theorem ramificationIdx_span_zeta_sub_one' :
    ramificationIdx' (span {hζ.toInteger - 1}) ℤ = p - 1 := by
  rw [← pow_one p] at hK hζ
  rw [ramificationIdx_span_zeta_sub_one p 0 hζ, pow_zero, one_mul]

variable (K)

include hK in
theorem ncard_primesOver_of_prime :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  rw [← pow_one p] at hK
  exact ncard_primesOver_of_prime_pow p 0 K

theorem eq_span_zeta_sub_one_of_liesOver' (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    P = span {hζ.toInteger - 1} := by
  rw [← pow_one p] at hK hζ
  exact eq_span_zeta_sub_one_of_liesOver p 0 K hζ P

include hK in
theorem inertiaDeg_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    inertiaDeg' P ℤ = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P, inertiaDeg_span_zeta_sub_one']

include hK in
theorem ramificationIdx_eq_of_prime (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver 𝒑] :
    ramificationIdx' P ℤ = p - 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver' p K hK.zeta_spec P, ramificationIdx_span_zeta_sub_one']

include hK in
theorem inertiaDegIn_eq_of_prime :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  rw [← pow_one p] at hK
  exact inertiaDegIn_eq_of_prime_pow p 0 K

include hK in
theorem ramificationIdxIn_eq_of_prime :
    𝒑.ramificationIdxIn (𝓞 K) = p - 1 := by
  rw [← pow_one p] at hK
  rw [ramificationIdxIn_eq_of_prime_pow p 0, pow_zero, one_mul]

@[deprecated (since := "2025-12-03")] alias ramificationIdxIn_of_prime :=
  ramificationIdxIn_eq_of_prime

end Prime

section notDvd

open NumberField.Ideal Polynomial

variable {m} [NeZero m] [hK : IsCyclotomicExtension {m} ℚ K]

theorem inertiaDeg_eq_of_not_dvd (hm : ¬ p ∣ m) :
    inertiaDeg' P ℤ = orderOf (p : ZMod m) := by
  replace hm : p.Coprime m := hp.out.coprime_iff_not_dvd.mpr hm
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  have : P.IsMaximal := .of_liesOver_isMaximal P 𝒑
  rw [← inertiaDeg_eq_inertiaDeg' 𝒑]
  rw [h₃, natDegree_of_dvd_cyclotomic_of_irreducible (by simp) hm (f := 1) _ h₂.1]
  · simpa using (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
  · refine dvd_trans h₂.2.2 ?_
    rw [← map_cyclotomic_int, cyclotomic_eq_minpoly (zeta_spec m ℚ K) (NeZero.pos _),
      ← (zeta_spec m ℚ K).coe_toInteger, ← RingOfIntegers.minpoly_coe ζ]
    simp [ζ]

@[deprecated (since := "2025-12-10")]
alias inertiaDeg_of_not_dvd := inertiaDeg_eq_of_not_dvd

theorem ramificationIdx_eq_of_not_dvd (hm : ¬ p ∣ m) :
    ramificationIdx' P ℤ = 1 := by
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [← ramificationIdx_eq_ramificationIdx' 𝒑 P (by simpa using hp.out.ne_zero), h₃]
  refine multiplicity_eq_of_emultiplicity_eq_some (le_antisymm ?_ ?_)
  · apply emultiplicity_le_one_of_separable
    · exact isUnit_iff_degree_eq_zero.not.mpr (Irreducible.degree_pos h₂.1).ne'
    · exact (zeta_spec m ℚ K).toInteger_isPrimitiveRoot.separable_minpoly_mod hm
  · rw [ENat.coe_one]
    exact Order.one_le_iff_pos.mpr <| emultiplicity_pos_of_dvd h₂.2.2

@[deprecated (since := "2025-12-10")]
alias ramificationIdx_of_not_dvd := ramificationIdx_eq_of_not_dvd

theorem inertiaDegIn_eq_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) := by
  have : IsGalois ℚ K := isGalois {m} ℚ K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/ℚ), inertiaDeg_eq_of_not_dvd p K P hm]

theorem ramificationIdxIn_eq_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = 1 := by
  have : IsGalois ℚ K := isGalois {m} ℚ K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/ℚ), ramificationIdx_eq_of_not_dvd p K P hm]

@[deprecated (since := "2025-12-03")] alias inertiaDegIn_of_not_dvd := inertiaDegIn_eq_of_not_dvd
@[deprecated (since := "2025-12-03")] alias ramificationIdxIn_of_not_dvd :=
  ramificationIdxIn_eq_of_not_dvd

end notDvd

section general

variable {m p k} [IsCyclotomicExtension {n} ℚ K]

set_option backward.isDefEq.respectTransparency false in
open IntermediateField in
private theorem inertiaDegIn_ramificationIdxIn_aux (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) ∧
      𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {n} ℚ K
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  have : NeZero n := ⟨hn ▸ NeZero.ne (p ^ (k + 1) * m)⟩
  let ζ := zeta n ℚ K
  have hζ := zeta_spec n ℚ K
  -- We construct `ℚ⟮ζₘ⟯ ⊆ ℚ⟮ζₙ⟯`
  let ζₘ := ζ ^ (p ^ (k + 1))
  have hζₘ := hζ.pow (NeZero.pos _) hn
  let Fₘ := ℚ⟮ζₘ⟯
  have : IsCyclotomicExtension {m} ℚ Fₘ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₘ).mpr rfl
  -- A prime ideal of `Fₘ` above `𝒑`
  obtain ⟨Pₘ, _, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral 𝒑 (S := 𝓞 Fₘ)
  -- We construct `ℚ⟮ζ_p^{k+1}⟯ ⊆ ℚ⟮ζₘ⟯`
  let ζₚ := ζ ^ m
  have hζₚ := hζ.pow (NeZero.pos _) (mul_comm _ m ▸ hn)
  let Fₚ := ℚ⟮ζₚ⟯
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ Fₚ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₚ).mpr rfl
  -- A prime ideal of `Fₚ` above `𝒑`
  obtain ⟨Pₚ, hP₁, _⟩ := exists_maximal_ideal_liesOver_of_isIntegral 𝒑 (S := 𝓞 Fₚ)
  suffices Pₚ.ramificationIdxIn (𝓞 K) *
      Pₘ.inertiaDegIn (𝓞 K) * (Pₘ.primesOver (𝓞 K)).ncard = 1 by
    replace this := Nat.eq_one_of_mul_eq_one_right this
    rw [← inertiaDegIn_mul_inertiaDegIn 𝒑 Pₘ Gal(Fₘ/ℚ) _ Gal(K/ℚ) Gal(K/Fₘ),
      ← ramificationIdxIn_mul_ramificationIdxIn Pₚ Gal(Fₚ/ℚ) _ Gal(K/ℚ) Gal(K/Fₚ),
      Nat.eq_one_of_mul_eq_one_left this, Nat.eq_one_of_mul_eq_one_right this, mul_one, mul_one,
      inertiaDegIn_eq_of_not_dvd p _ hm, ramificationIdxIn_eq_of_prime_pow p k Fₚ]
    exact ⟨rfl, rfl⟩
  have h_main : Module.finrank ℚ Fₘ * Module.finrank ℚ Fₚ = Module.finrank ℚ K := by
    rw [finrank m, finrank (p ^ (k + 1)), finrank n, hn, mul_comm, Nat.totient_mul]
    exact Nat.Coprime.pow_left (k + 1) (by rwa [hp.out.coprime_iff_not_dvd])
  rwa [← IsGalois.card_aut_eq_finrank, ← IsGalois.card_aut_eq_finrank,
    ← IsGalois.card_aut_eq_finrank,
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 Fₘ) Gal(Fₘ/ℚ),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 Fₚ) Gal(Fₚ/ℚ),
    ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝒑 (𝓞 K) Gal(K/ℚ),
    ← ncard_primesOver_mul_ncard_primesOver Pₘ Gal(Fₘ/ℚ) (𝓞 K) Gal(K/ℚ) Gal(K/Fₘ),
    ramificationIdxIn_eq_of_not_dvd p Fₘ hm, inertiaDegIn_eq_of_prime_pow p k Fₚ,
    ncard_primesOver_of_prime_pow p k Fₚ, one_mul, one_mul, mul_one, mul_assoc, mul_assoc,
    mul_right_inj' (IsDedekindDomain.primesOver_ncard_ne_zero 𝒑 _), ← mul_assoc,
    ← mul_rotate (𝒑.inertiaDegIn (𝓞 K)),
    ← inertiaDegIn_mul_inertiaDegIn 𝒑 Pₘ Gal(Fₘ/ℚ) (𝓞 K) Gal(K/ℚ) Gal(K/Fₘ), mul_assoc, mul_assoc,
    mul_right_inj' (inertiaDegIn_ne_zero Gal(Fₘ/ℚ)), ← mul_rotate',
    ← ramificationIdxIn_mul_ramificationIdxIn (p := 𝒑) Pₚ Gal(Fₚ/ℚ) (𝓞 K) Gal(K/ℚ) Gal(K/Fₚ),
    eq_comm, mul_assoc, mul_eq_left₀ (ramificationIdxIn_ne_zero Gal(Fₚ/ℚ)), ← mul_assoc]
    at h_main

/--
Write `n = p ^ (k + 1) * m` where the prime `p` does not divide `m`, then the inertia degree of
`p` in `ℚ(ζₙ)` is the order of `p` modulo `m`.
-/
theorem inertiaDegIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) :=
  (inertiaDegIn_ramificationIdxIn_aux n K hn hm).1

/--
Write `n = p ^ (k + 1) * m` where the prime `p` does not divide `m`, then the ramification index
of `p` in `ℚ(ζₙ)` is `p ^ k * (p - 1)`.
-/
theorem ramificationIdxIn_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) :=
  (inertiaDegIn_ramificationIdxIn_aux n K hn hm).2

theorem inertiaDeg_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    inertiaDeg' P ℤ = orderOf (p : ZMod m) := by
  have : IsGalois ℚ K := isGalois {n} ℚ K
  rw [← inertiaDegIn_eq_inertiaDeg 𝒑 P Gal(K/ℚ), inertiaDegIn_eq n K hn hm]

theorem ramificationIdx_eq (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    ramificationIdx' P ℤ = p ^ k * (p - 1) := by
  have : IsGalois ℚ K := isGalois {n} ℚ K
  rw [← ramificationIdxIn_eq_ramificationIdx 𝒑 P Gal(K/ℚ), ramificationIdxIn_eq n K hn hm]

end general

end IsCyclotomicExtension.Rat

/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
import Mathlib.RingTheory.Polynomial.Cyclotomic.Factorization
import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
import Mathlib.RingTheory.Ideal.GoingUp

/-!
# Ideals in cyclotomic fields

In this file, we prove results about ideals in cyclotomic extensions of `ℚ`.

## Main results

* `IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow`: there is only one prime ideal above
  the prime `p` in `ℚ(ζ_pᵏ)`

* `IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow`: the inertia degree of the prime ideal
  above `p` in `ℚ(ζ_pᵏ)` is `1`.

* `IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime_pow`: the ramification index of the prime
  ideal above `p` in `ℚ(ζ_pᵏ)` is `p ^ (k - 1) * (p - 1)`.

* `IsCyclotomicExtension.Rat.inertiaDeg_of_not_dvd`: if the prime `p` does not divide `m`, then
  the inertia degree of `p` in `ℚ(ζₘ)` if the order of `p` modulo `m`.

* `IsCyclotomicExtension.Rat.ramificationIdx_of_not_dvd`: if the prime `p` does not divide `m`,
  then the ramification index of `p` in `ℚ(ζₘ)` is `1`.

-/

namespace IsCyclotomicExtension.Rat

open Ideal NumberField RingOfIntegers

variable (n m p k : ℕ) [hp : Fact (Nat.Prime p)] (K : Type*) [Field K] [NumberField K]
  (P : Ideal (𝓞 K)) [hP₁ : P.IsPrime] [hP₂ : P.LiesOver (Ideal.span {(p : ℤ)})]

local notation3 "𝒑" => (Ideal.span {(p : ℤ)})

section PrimePow

variable {K} [hK : IsCyclotomicExtension {p ^ (k + 1)} ℚ K] {ζ : K}
  (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))

instance isPrime_span_zeta_sub_one : IsPrime (span {hζ.toInteger - 1}) := by
  rw [Ideal.span_singleton_prime]
  · exact hζ.zeta_sub_one_prime
  · exact Prime.ne_zero hζ.zeta_sub_one_prime

theorem associated_norm_zeta_sub_one : Associated (Algebra.norm ℤ (hζ.toInteger - 1)) (p : ℤ) := by
  by_cases h : p = 2
  · cases k with
    | zero =>
      rw [h, zero_add, pow_one] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two, h, Int.ofNat_two, Associated.neg_left_iff]
    | succ n =>
      rw [h, add_assoc, show 1 + 1 = 2 by rfl] at hK hζ
      rw [hζ.norm_toInteger_sub_one_of_eq_two_pow, h, Int.ofNat_two]
  · rw [hζ.norm_toInteger_sub_one_of_prime_ne_two h]

theorem absNorm_span_zeta_sub_one : absNorm (span {hζ.toInteger - 1}) = p := by
  simpa using congr_arg absNorm <|
    span_singleton_eq_span_singleton.mpr <| associated_norm_zeta_sub_one p k hζ

theorem p_mem_span_zeta_sub_one : (p : 𝓞 K) ∈ span {hζ.toInteger - 1} := by
  convert Ideal.absNorm_mem _
  exact (absNorm_span_zeta_sub_one ..).symm

theorem span_zeta_sub_one_ne_bot : span {hζ.toInteger - 1} ≠ ⊥ :=
  (Submodule.ne_bot_iff _).mpr ⟨p, p_mem_span_zeta_sub_one p k hζ, NeZero.natCast_ne p (𝓞 K)⟩

instance liesOver_span_zeta_sub_one : (span {hζ.toInteger - 1}).LiesOver 𝒑 := by
  rw [liesOver_iff]
  refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p) IsPrime.ne_top' ?_
  rw [span_singleton_le_iff_mem, mem_comap, algebraMap_int_eq, map_natCast]
  exact p_mem_span_zeta_sub_one p k hζ

theorem inertiaDeg_span_zeta_sub_one : inertiaDeg 𝒑 (span {hζ.toInteger - 1}) = 1 := by
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
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 (span {hζ.toInteger - 1}) = p ^ k * (p - 1) := by
  have h := isPrime_span_zeta_sub_one p k hζ
  rw [← Nat.totient_prime_pow_succ hp.out, ← finrank _ K,
    IsDedekindDomain.ramificationIdx_eq_multiplicity _ h, map_eq_span_zeta_sub_one_pow p k hζ,
    multiplicity_pow_self (span_zeta_sub_one_ne_bot p k hζ) (isUnit_iff.not.mpr h.ne_top)]
  exact map_ne_bot_of_ne_bot <| by simpa using hp.out.ne_zero

variable (K)

include hK in
theorem ncard_primesOver_of_prime_pow :
    (primesOver 𝒑 (𝓞 K)).ncard = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  have : 𝒑 ≠ ⊥ := by simpa using hp.out.ne_zero
  have h_main := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn this (𝓞 K) ℚ K
  have hζ := hK.zeta_spec
  rwa [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hζ.toInteger - 1}) ℚ K,
    inertiaDegIn_eq_inertiaDeg 𝒑 (span {hζ.toInteger - 1}) ℚ K, inertiaDeg_span_zeta_sub_one,
    ramificationIdx_span_zeta_sub_one, mul_one, ← Nat.totient_prime_pow_succ hp.out,
    ← finrank _ K, Nat.mul_eq_right] at h_main
  exact Module.finrank_pos.ne'

theorem eq_span_zeta_sub_one_of_liesOver :
    P = span {hζ.toInteger - 1} := by
  have : P ∈ primesOver 𝒑 (𝓞 K) := ⟨hP₁, hP₂⟩
  have : span {hζ.toInteger - 1} ∈ primesOver 𝒑 (𝓞 K) :=
    ⟨isPrime_span_zeta_sub_one p k hζ, liesOver_span_zeta_sub_one p k hζ⟩
  have := ncard_primesOver_of_prime_pow p k K
  aesop

include hK in
theorem inertiaDeg_eq_of_prime_pow :
    inertiaDeg 𝒑 P = 1 := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K P hK.zeta_spec, inertiaDeg_span_zeta_sub_one]

include hK in
theorem ramificationIdx_eq_of_prime_pow :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p ^ k * (p - 1) := by
  rw [eq_span_zeta_sub_one_of_liesOver p k K P hK.zeta_spec, ramificationIdx_span_zeta_sub_one]

include hK in
theorem inertiaDegIn_of_prime_pow :
    𝒑.inertiaDegIn (𝓞 K) = 1 := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 (span {hK.zeta_spec.toInteger - 1}) ℚ K,
    inertiaDeg_span_zeta_sub_one]

include hK in
theorem ramificationIdxIn_of_prime_pow :
    𝒑.ramificationIdxIn (𝓞 K) = p ^ k * (p - 1) := by
  have : IsGalois ℚ K := isGalois {p ^ (k + 1)} ℚ K
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 (span {hK.zeta_spec.toInteger - 1}) ℚ K,
    ramificationIdx_span_zeta_sub_one]

end PrimePow

section notDVD

open NumberField.Ideal Polynomial

variable [NeZero m] [hK : IsCyclotomicExtension {m} ℚ K]

theorem inertiaDeg_of_not_dvd (hm : ¬ p ∣ m) :
    inertiaDeg 𝒑 P = orderOf (p : ZMod m) := by
  replace hm : p.Coprime m := not_not.mp <| (Nat.Prime.dvd_iff_not_coprime hp.out).not.mp hm
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top m K (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [h₃, natDegree_of_dvd_cyclotomic_of_irreducible (by simp) hm (f := 1) _ h₂.1]
  · simpa using (orderOf_injective _ Units.coeHom_injective (ZMod.unitOfCoprime p hm)).symm
  · refine dvd_trans h₂.2.2 ?_
    rw [← map_cyclotomic_int, cyclotomic_eq_minpoly (zeta_spec m ℚ K) (NeZero.pos _),
      ← (zeta_spec m ℚ K).coe_toInteger, ← RingOfIntegers.minpoly_coe ζ]
    rfl

theorem ramificationIdx_of_not_dvd (hm : ¬ p ∣ m) :
    ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = 1 := by
  let ζ := (zeta_spec m ℚ K).toInteger
  have h₁ : ¬ p ∣ exponent ζ := by
    rw [exponent_eq_one_iff.mpr <| adjoin_singleton_eq_top m K (zeta_spec m ℚ K)]
    exact hp.out.not_dvd_one
  have h₂ := (primesOverSpanEquivMonicFactorsMod h₁ ⟨P, ⟨inferInstance, inferInstance⟩⟩).2
  have h₃ := ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply' h₁ h₂
  simp only [Subtype.coe_eta, Equiv.symm_apply_apply] at h₃
  rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff
    (map_monic_ne_zero (minpoly.monic ζ.isIntegral))] at h₂
  rw [h₃]
  refine multiplicity_eq_of_emultiplicity_eq_some (le_antisymm ?_ ?_)
  · apply emultiplicity_le_one_of_separable
    · exact isUnit_iff_degree_eq_zero.not.mpr (Irreducible.degree_pos h₂.1).ne'
    · exact (zeta_spec m ℚ K).toInteger_isPrimitiveRoot.separable_minpoly_mod hm
  · rw [ENat.coe_one]
    exact Order.one_le_iff_pos.mpr <| emultiplicity_pos_of_dvd h₂.2.2

theorem inertiaDegIn_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.inertiaDegIn (𝓞 K) = orderOf (p : ZMod m) := by
  have : IsGalois ℚ K := isGalois {m} ℚ K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [inertiaDegIn_eq_inertiaDeg 𝒑 P ℚ K, inertiaDeg_of_not_dvd m p K P hm]

theorem ramificationIdxIn_of_not_dvd (hm : ¬ p ∣ m) :
    𝒑.ramificationIdxIn (𝓞 K) = 1 := by
  have : IsGalois ℚ K := isGalois {m} ℚ K
  obtain ⟨⟨P, _, _⟩⟩ := 𝒑.nonempty_primesOver (S := 𝓞 K)
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 P ℚ K, ramificationIdx_of_not_dvd m p K P hm]

end notDVD

section generalCase

variable [IsCyclotomicExtension {n} ℚ K]

open IntermediateField

theorem inertiaDeg_ramificationIdx (hn : n = p ^ (k + 1) * m) (hm : ¬ p ∣ m) :
    inertiaDeg 𝒑 P = orderOf (p : ZMod m) ∧
      ramificationIdx (algebraMap ℤ (𝓞 K)) 𝒑 P = p ^ k * (p - 1) := by
  have : IsAbelianGalois ℚ K := IsCyclotomicExtension.isAbelianGalois {n} ℚ K
  have : NeZero m := ⟨fun h ↦ by simp [h] at hm⟩
  have : NeZero n := by exact ⟨hn ▸ NeZero.ne (p ^ (k + 1) * m)⟩
  have : P.IsMaximal := sorry
  let ζ := zeta n ℚ K
  have hζ := zeta_spec n ℚ K
  -- Root of unity of order `m`
  let ζₘ := ζ ^ (p ^ (k + 1))
  have hζₘ := hζ.pow (NeZero.pos _) hn
  let Fₘ := ℚ⟮ζₘ⟯
  have : IsCyclotomicExtension {m} ℚ Fₘ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₘ).mpr rfl
  -- The prime ideal of `ℚ⟮ζₘ⟯` below `P`
  let Pₘ := comap (algebraMap (𝓞 Fₘ) (𝓞 K)) P
  have : Pₘ.IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal _
  -- Root of unity of order `p ^ (k + 1)`
  let ζₚ := ζ ^ m
  have hζₚ := hζ.pow (NeZero.pos _) (mul_comm _ m ▸ hn)
  let Fₚ := ℚ⟮ζₚ⟯
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ Fₚ :=
    (isCyclotomicExtension_singleton_iff_eq_adjoin _ _ _ _ hζₚ).mpr rfl
  -- The prime ideal of `ℚ⟮ζₚ⟯` below `P`
  let Pₚ := comap (algebraMap (𝓞 Fₚ) (𝓞 K)) P
  have : Pₚ.IsMaximal := isMaximal_comap_of_isIntegral_of_isMaximal _
  have h₁ := ramificationIdx_algebra_tower (p := 𝒑) (P := Pₚ) (Q := P)
    (by
      refine map_ne_bot_of_ne_bot ?_
      apply Ring.ne_bot_of_isMaximal_of_not_isField inferInstance (not_isField Fₚ))
    (by
      apply map_ne_bot_of_ne_bot
      simpa using hp.out.ne_zero)
    (by
      apply Ideal.map_comap_le)
--  rw [ramificationIdx_eq_of_prime_pow p k Fₚ] at h₁
  have h₂ := inertiaDeg_algebra_tower 𝒑 Pₘ P
  suffices (Pₘ.primesOver (𝓞 K)).ncard *
      (Pₘ.inertiaDeg P * ramificationIdx (algebraMap (𝓞 ↥Fₚ) (𝓞 K)) Pₚ P) = 1 by
    replace this := Nat.eq_one_of_mul_eq_one_left this
    rw [ramificationIdx_eq_of_prime_pow p k Fₚ] at h₁ -- FIX THIS
    rw [h₁, inertiaDeg_algebra_tower 𝒑 Pₘ P, inertiaDeg_of_not_dvd m _ Fₘ Pₘ hm,
      Nat.eq_one_of_mul_eq_one_left this, Nat.eq_one_of_mul_eq_one_right this, mul_one, mul_one]
    exact Nat.pair_eq_pair.mp rfl
  have h₃ : (𝒑.primesOver (𝓞 Fₘ)).ncard * (Pₘ.primesOver (𝓞 K)).ncard =
      (𝒑.primesOver (𝓞 K)).ncard := by
    sorry
    -- rw [ncard_primesOver_eq_sum_ncard_primesOver ℤ (𝓞 Fₘ)]
    -- conv_lhs =>
    --   enter [2, P]
    --   rw [ncard_primesOver_eq_ncard_primesOver ℚ Fₘ K 𝒑 P.val Pₘ]
    -- rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
    -- rw [← Set.toFinset_card, ← Set.ncard_eq_toFinset_card']
  rw [← Nat.mul_eq_right (Module.finrank_pos (R := ℚ) (M := K)).ne']
  calc
    _ = (Pₘ.primesOver (𝓞 K)).ncard *
          (Pₘ.inertiaDeg P * ramificationIdx (algebraMap (𝓞 Fₚ) (𝓞 K)) Pₚ P) *
          (Module.finrank ℚ Fₚ * ((𝒑.primesOver (𝓞 Fₘ)).ncard * 𝒑.inertiaDegIn (𝓞 Fₘ))) := ?_
    _ = ((𝒑.primesOver (𝓞 Fₘ)).ncard * (Pₘ.primesOver (𝓞 K)).ncard) *
          (𝒑.ramificationIdxIn (𝓞 Fₚ) * ramificationIdx (algebraMap (𝓞 Fₚ) (𝓞 K)) Pₚ P) *
          (𝒑.inertiaDegIn (𝓞 Fₘ) * Pₘ.inertiaDeg P) := ?_
    _ = Module.finrank ℚ K := ?_
  · rw [finrank n K, hn, Nat.totient_mul, ← finrank _ Fₚ, ← finrank _ Fₘ,
      ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
      (by simpa using hp.out.ne_zero) (𝓞 Fₘ) ℚ Fₘ, ramificationIdxIn_of_not_dvd m p Fₘ hm, one_mul]
    refine Nat.Coprime.pow_left (k + 1) ?_
    exact not_not.mp <| (Nat.Prime.dvd_iff_not_coprime hp.out).not.mp hm
  · rw [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
      (by simpa using hp.out.ne_zero) (𝓞 Fₚ) ℚ Fₚ, inertiaDegIn_of_prime_pow p k Fₚ,
      ncard_primesOver_of_prime_pow p k Fₚ, mul_one, one_mul]
    ring
  · rw [h₃, ramificationIdxIn_eq_ramificationIdx 𝒑 Pₚ ℚ Fₚ, ← h₁,
      inertiaDegIn_eq_inertiaDeg 𝒑 Pₘ ℚ Fₘ, ← h₂, ← ramificationIdxIn_eq_ramificationIdx 𝒑 P ℚ K,
      ← inertiaDegIn_eq_inertiaDeg 𝒑 P ℚ K, mul_assoc,
      ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn _ (𝓞 K) ℚ K]
    simpa using hp.out.ne_zero


#exit

  rw [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
    (by simpa using hp.out.ne_zero) (𝓞 Fₘ) ℚ Fₘ]
  rw [← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
    (by simpa using hp.out.ne_zero) (𝓞 Fₚ) ℚ Fₚ]
  rw [inertiaDegIn_of_prime_pow p k Fₚ]
  rw [ramificationIdxIn_of_not_dvd m p Fₘ]
  rw [one_mul, mul_one]








#exit

  rw [finrank n K, hn, Nat.totient_mul, Nat.totient_prime_pow, add_tsub_cancel_right,
    ramificationIdxIn_eq_ramificationIdx 𝒑 P ℚ K, inertiaDegIn_eq_inertiaDeg 𝒑 P ℚ K, h₁, h₃]
    at h_main
  rw [← finrank m Fₘ, ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
    (by simpa using hp.out.ne_zero) (𝓞 Fₘ) ℚ Fₘ] at h_main
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 Pₘ ℚ Fₘ] at h_main
  rw [ramificationIdx_of_not_dvd m p Fₘ, one_mul] at h_main
  rw [h₂, inertiaDegIn_eq_inertiaDeg 𝒑 Pₘ ℚ Fₘ, ← mul_assoc, ← mul_assoc,
    mul_assoc _ _ (𝒑.inertiaDeg Pₘ)] at h_main


  rw [← finrank m Fₘ, ← ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (p := 𝒑)
    (by simpa using hp.out.ne_zero) (𝓞 Fₘ) ℚ Fₘ] at h_main
  rw [Nat.mul_right_inj] at h_main
  rw [Nat.mul_right_inj] at h_main
  rw [ramificationIdxIn_eq_ramificationIdx 𝒑 Pₘ ℚ Fₘ] at h_main
  rw [ramificationIdx_of_not_dvd m p Fₘ, one_mul] at h_main
  rw [h₂, inertiaDegIn_eq_inertiaDeg 𝒑 Pₘ ℚ Fₘ, ← mul_assoc, ← mul_assoc,
    mul_assoc _ _ (𝒑.inertiaDeg Pₘ)] at h_main
  rw [ Nat.mul_eq_right] at h_main
end generalCase

end IsCyclotomicExtension.Rat

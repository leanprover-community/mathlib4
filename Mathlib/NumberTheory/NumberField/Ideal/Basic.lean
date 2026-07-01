/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.NumberTheory.NumberField.Units.Basic

/-!
# Basic results on integral ideals of a number field

We study results about integral ideals of a number field `K`.

## Main definitions and results

* `Ideal.rootsOfUnityMapQuot` : For `I` an integral ideal of `K`, the group morphism from the
  group of roots of unity of `K` of order `n` to `(𝓞 K ⧸ I)ˣ`.

* `Ideal.rootsOfUnityMapQuot_injective`: If the ideal `I` is nontrivial and its norm is coprime
  with `n`, then the map `Ideal.rootsOfUnityMapQuot` is injective.

* `NumberField.torsionOrder_dvd_absNorm_sub_one`: If the norm of the (nonzero) prime ideal `P` is
  coprime with the order of the torsion of `K`, then the norm of `P` is congruent to `1` modulo
  `torsionOrder K`.

* `NumberField.torsionOrder_dvd_absNorm_sub_one'`: If the prime ideal `P` is unramified over `ℤ`
  and the norm of the prime of `ℤ` lying under `P` is greater than `2`, then the norm of `P` is
  congruent to `1` modulo `torsionOrder K`.

-/

@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

theorem IsPrimitiveRoot.not_coprime_norm_of_mk_eq_one [NumberField K] (hI : absNorm I ≠ 1) {n : ℕ}
    {ζ : K} (hn : 2 ≤ n) (hζ : IsPrimitiveRoot ζ n)
    (h : letI _ : NeZero n := NeZero.of_gt hn; Ideal.Quotient.mk I hζ.toInteger = 1) :
    ¬ (absNorm I).Coprime n := by
  intro h₁
  rw [← map_one (Ideal.Quotient.mk I), Ideal.Quotient.eq] at h
  obtain ⟨p, hp, h₂⟩ := Nat.exists_prime_and_dvd hI
  have : Fact (p.Prime) := ⟨hp⟩
  refine hp.not_dvd_one <| h₁ ▸ Nat.dvd_gcd h₂ ?_
  exact hζ.prime_dvd_of_dvd_norm_sub_one hn <|
    Int.dvd_trans (Int.natCast_dvd_natCast.mpr h₂) (absNorm_dvd_norm_of_mem h)

variable (I)

/--
For `I` an integral ideal of `K`, the group morphism from the group of roots of unity of `K`
of order `n` to `(𝓞 K ⧸ I)ˣ`.
-/
def Ideal.rootsOfUnityMapQuot (n : ℕ) : (rootsOfUnity n (𝓞 K)) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict _

@[simp]
theorem Ideal.rootsOfUnityMapQuot_apply (n : ℕ) {x : (𝓞 K)ˣ} (hx : x ∈ rootsOfUnity n (𝓞 K)) :
    rootsOfUnityMapQuot I n ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

/--
For `I` an integral ideal of `K`, the group morphism from the torsion of `K` to `(𝓞 K ⧸ I)ˣ`.
-/
def Ideal.torsionMapQuot : (Units.torsion K) →* ((𝓞 K) ⧸ I)ˣ :=
  (Units.map (Ideal.Quotient.mk I).toMonoidHom).restrict (torsion K)

@[simp]
theorem Ideal.torsionMapQuot_apply {x : (𝓞 K)ˣ} (hx : x ∈ torsion K) :
    torsionMapQuot I ⟨x, hx⟩ = Ideal.Quotient.mk I x := rfl

variable {I} [NumberField K]

theorem Ideal.rootsOfUnityMapQuot_injective (n : ℕ) [NeZero n] (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime n) :
    Function.Injective (rootsOfUnityMapQuot I n) := by
  refine (injective_iff_map_eq_one _).mpr fun ⟨ζ, hζ⟩ h ↦ ?_
  obtain ⟨t, ht₀, ht, hζ⟩ := isPrimitiveRoot_of_mem_rootsOfUnity hζ
  suffices ¬ (2 ≤ t) by
    simpa [show t = 1 by grind] using hζ
  intro ht'
  let μ : K := ζ.val
  have hμ : IsPrimitiveRoot μ t :=
    (IsPrimitiveRoot.coe_units_iff.mpr hζ).map_of_injective RingOfIntegers.coe_injective
  rw [Units.ext_iff, rootsOfUnityMapQuot_apply, Units.val_one] at h
  refine hμ.not_coprime_norm_of_mk_eq_one hI₁ ht' h ?_
  exact Nat.dvd_one.mp (hI₂ ▸ Nat.gcd_dvd_gcd_of_dvd_right (absNorm I) ht)

theorem IsPrimitiveRoot.idealQuotient_mk {n : ℕ} [NeZero n] {ζ : (𝓞 K)} (hζ : IsPrimitiveRoot ζ n)
    (hI₁ : absNorm I ≠ 1) (hI₂ : (absNorm I).Coprime n) :
    IsPrimitiveRoot (Ideal.Quotient.mk I ζ) n := by
  have h : IsPrimitiveRoot hζ.toRootsOfUnity n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp <| IsPrimitiveRoot.coe_units_iff.mp hζ
  exact IsPrimitiveRoot.coe_units_iff.mpr <|
    h.map_of_injective <| Ideal.rootsOfUnityMapQuot_injective n hI₁ hI₂

/--
If the ideal `I` is nontrivial and its norm is coprime with `torsionOrder K`, then the map
`Ideal.torsionMapQuot` is injective.
-/
theorem Ideal.torsionMapQuot_injective (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) :
    Function.Injective (torsionMapQuot I) := by
  intro ⟨x, hx⟩ ⟨y, hy⟩ h
  rw [← rootsOfUnity_eq_torsion] at hx hy
  rw [Subtype.mk_eq_mk, ← Subtype.mk_eq_mk (h := hx) (h' := hy)]
  exact rootsOfUnityMapQuot_injective (torsionOrder K) hI₁ hI₂ h

open IntermediateField in
/--
If the prime ideal `P` is unramified over `ℤ` and the norm of the prime of `ℤ` lying under `P` is
greater than `2`, then the map `Ideal.torsionMapQuot` is injective.
-/
theorem Ideal.torsionMapQuot_injective' {P : Ideal (𝓞 K)} [hP : P.IsPrime]
    (hP₁ : Algebra.IsUnramifiedAt ℤ P) (hP₂ : 2 < absNorm (under ℤ P)) :
    Function.Injective P.torsionMapQuot := by
  have : NeZero P := ⟨fun h ↦ by simp [h] at hP₂⟩
  rw [injective_iff_map_eq_one]
  by_contra!
  obtain ⟨⟨ζ, hζ₀⟩, hζ₁, hζ₂⟩ := this
  obtain ⟨n, hn, hζ₃⟩ : ∃ n, 2 ≤ n ∧ IsPrimitiveRoot (ζ : K) n := by
    refine ⟨orderOf ζ, ?_, IsPrimitiveRoot.coe_coe_iff.mpr (IsPrimitiveRoot.orderOf ζ)⟩
    rw [Nat.two_le_iff, orderOf_ne_zero_iff]
    exact ⟨hζ₀, by simpa using hζ₂⟩
  have h_cpr := hζ₃.not_coprime_norm_of_mk_eq_one
    (absNorm_eq_one_iff.not.mpr <| IsPrime.ne_top hP) hn
    (by rwa [Units.ext_iff, torsionMapQuot_apply, val_one] at hζ₁)
  let p := (Ideal.under ℤ P).absNorm
  have hp := Nat.absNorm_under_prime P
  have : Fact p.Prime := ⟨hp⟩
  rw [P.absNorm_eq_pow_inertiaDeg' hp, Nat.coprime_pow_left_iff (Ideal.inertiaDeg_pos _ _),
    ← Nat.Prime.dvd_iff_not_coprime hp] at h_cpr
  obtain ⟨c, hc⟩ := h_cpr
  have hζ_pow := IsPrimitiveRoot.pow (by grind) hζ₃ (by rwa [mul_comm])
  let F := ℚ⟮(ζ : K) ^ c⟯
  have : IsCyclotomicExtension {p} ℚ F :=
    hζ_pow.intermediateField_adjoin_isCyclotomicExtension ℚ
  suffices 1 < P.ramificationIdx' ℤ by
    rwa [P.ramificationIdx'_eq_one ℤ, lt_self_iff_false] at this
  rw [Ideal.ramificationIdx'_tower (P.under (𝓞 F)) P,
    IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p F]
  exact one_lt_mul_of_lt_of_le (by rwa [Nat.lt_sub_iff_add_lt']) <| P.ramificationIdx'_pos (𝓞 F)

/--
If the norm of the (nonzero) prime ideal `P` is coprime with the order of the torsion of `K`, then
the norm of `P` is congruent to `1` modulo `torsionOrder K`.
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one {P : Ideal (𝓞 K)} (hP₀ : P ≠ ⊥)
    (hP₁ : P.IsPrime) (hP₂ : (absNorm P).Coprime (torsionOrder K)) :
    torsionOrder K ∣ absNorm P - 1 := by
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP₁
  let _ := Ideal.Quotient.field P
  have hP₃ : absNorm P ≠ 1 := absNorm_eq_one_iff.not.mpr <| IsPrime.ne_top hP₁
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective hP₃ hP₂)
  rwa [Nat.card_eq_fintype_card, Nat.card_units] at h

/--
If the prime ideal `P` is unramified over `ℤ` and the norm of the prime of `ℤ` lying under `P` is
greater than `2`, then the norm of `P` is congruent to `1` modulo `torsionOrder K`.
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one' {P : Ideal (𝓞 K)} [hP : P.IsPrime] [NeZero P]
    (hP₁ : Algebra.IsUnramifiedAt ℤ P) (hP₂ : 2 < absNorm (under ℤ P)) :
    torsionOrder K ∣ absNorm P - 1 := by
  have hP₀ : P ≠ ⊥ := fun h ↦ by simp [h] at hP₂
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP
  let _ := Ideal.Quotient.field P
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective' hP₁ hP₂)
  rwa [Nat.card_eq_fintype_card, Nat.card_units] at h

end torsionMapQuot

instance [NumberField K] [I.IsMaximal] : Finite (𝓞 K ⧸ I) :=
  I.finiteQuotientOfFreeOfNeBot (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'

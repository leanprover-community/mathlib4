/-
Copyright (c) 2025 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
public import Mathlib.RingTheory.RootsOfUnity.Quotient

/-!
# Basic results on integral ideals of a number field

We study results about integral ideals of a number field `K`.

## Main definitions and results

* `Ideal.torsionMapQuot_injective`: If the ideal `I` is nontrivial and its norm is coprime
  with `torsionOrder K`, then the map `Ideal.torsionMapQuot` is injective.

* `NumberField.torsionOrder_dvd_absNorm_sub_one`: If the norm of the (nonzero) prime ideal `P` is
  coprime with the order of the torsion of `K`, then the norm of `P` is congruent to `1` modulo
  `torsionOrder K`.

* `NumberField.torsionOrder_dvd_absNorm_sub_one'`: If the prime ideal `P` is unramified over `ℤ`
  and the norm of the prime of `ℤ` lying under `P` is different from `2`, then the norm of `P` is
  congruent to `1` modulo `torsionOrder K`.

-/

@[expose] public section

open Ideal NumberField Units

variable {K : Type*} [Field K] {I : Ideal (𝓞 K)}

section torsionMapQuot

@[deprecated "use `IsPrimitiveRoot.not_coprime_absNorm_of_mk_eq_one`" (since := "2026-10-07")]
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

variable [NumberField K]

variable (I) in
/--
For `I` an integral ideal of `K`, the group morphism from the torsion of `K` to `(𝓞 K ⧸ I)ˣ`.
-/
noncomputable def Ideal.torsionMapQuot : (Units.torsion K) →* ((𝓞 K) ⧸ I)ˣ :=
  (rootsOfUnityMapQuot I (torsionOrder K)).comp
    (MulEquiv.subgroupCongr (rootsOfUnity_eq_torsion K).symm).toMonoidHom

variable (I) in
@[simp]
theorem Ideal.torsionMapQuot_apply {x : (𝓞 K)ˣ} (hx : x ∈ torsion K) :
    torsionMapQuot I ⟨x, hx⟩ = Ideal.Quotient.mk I x := by
  simp [torsionMapQuot]

/--
If the ideal `I` is nontrivial and its norm is coprime with `torsionOrder K`, then the map
`Ideal.torsionMapQuot` is injective.

See `Ideal.torsionMapQuot_injective'` for a version, with `I` a prime ideal, where this coprimality
is replaced by `I` being unramified over `ℤ`.
-/
theorem Ideal.torsionMapQuot_injective (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) :
    Function.Injective (torsionMapQuot I) :=
  (rootsOfUnityMapQuot_injective _ hI₁ hI₂).comp (MulEquiv.injective _)

theorem Ideal.torsionMapQuot_inj (hI₁ : absNorm I ≠ 1)
    (hI₂ : (absNorm I).Coprime (torsionOrder K)) {x y : torsion K} :
    torsionMapQuot I x = torsionMapQuot I y ↔ x = y :=
  (torsionMapQuot_injective hI₁ hI₂).eq_iff

open IntermediateField in
/--
If the prime ideal `P` is unramified over `ℤ` and the norm of the prime of `ℤ` lying under `P` is
greater than `2`, then the map `Ideal.torsionMapQuot` is injective.

See `Ideal.torsionMapQuot_injective` for a version where, instead, the norm of the ideal is
assumed coprime with `torsionOrder K`.
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
  let p := (Ideal.under ℤ P).absNorm
  have hp := Nat.absNorm_under_prime P
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨c, hc⟩ : p ∣ n := by
    have hnP : (n : 𝓞 K) ∈ P := by
      obtain ⟨d, hd⟩ := sub_one_dvd_natCast_of_pow_eq_one (ζ := ((ζ : (𝓞 K)ˣ) : 𝓞 K)) (n := n)
        (RingOfIntegers.coe_injective (by simpa using hζ₃.pow_eq_one))
        (fun h ↦ hζ₂ (Subtype.ext (Units.ext h)))
      rw [hd]
      refine P.mul_mem_right d ?_
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, sub_eq_zero]
      simpa [Units.ext_iff] using hζ₁
    have : (n : ℤ) ∈ under ℤ P := by simpa using hnP
    rw [← Int.ideal_span_absNorm_eq_self (under ℤ P), Ideal.mem_span_singleton] at this
    exact_mod_cast this
  have hζ_pow := IsPrimitiveRoot.pow (by positivity) hζ₃ (by rwa [mul_comm])
  let F := ℚ⟮(ζ : K) ^ c⟯
  have : IsCyclotomicExtension {p} ℚ F :=
    hζ_pow.intermediateField_adjoin_isCyclotomicExtension ℚ
  suffices 1 < P.ramificationIdx ℤ by
    rwa [P.ramificationIdx_eq_one ℤ, lt_self_iff_false] at this
  refine lt_of_lt_of_le ?_ <| ramificationIdx_below_le (P.under (𝓞 F)) P
  rwa [IsCyclotomicExtension.Rat.ramificationIdx_eq_of_prime p F, Nat.lt_sub_iff_add_lt']

theorem Ideal.torsionMapQuot_inj' {P : Ideal (𝓞 K)} [hP : P.IsPrime]
    (hP₁ : Algebra.IsUnramifiedAt ℤ P) (hP₂ : 2 < absNorm (under ℤ P)) {x y : torsion K} :
    P.torsionMapQuot x = P.torsionMapQuot y ↔ x = y :=
  (torsionMapQuot_injective' hP₁ hP₂).eq_iff

/--
If the norm of the (nonzero) prime ideal `P` is coprime with the order of the torsion of `K`, then
the norm of `P` is congruent to `1` modulo `torsionOrder K`.

See `NumberField.torsionOrder_dvd_absNorm_sub_one'` for a version where this coprimality is replaced
by `P` being unramified over `ℤ`.
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one {P : Ideal (𝓞 K)} (hP₀ : P ≠ ⊥)
    (hP₁ : P.IsPrime) (hP₂ : (absNorm P).Coprime (torsionOrder K)) :
    torsionOrder K ∣ absNorm P - 1 := by
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP₁
  let _ := Ideal.Quotient.field P
  have hP₃ : absNorm P ≠ 1 := absNorm_eq_one_iff.not.mpr <| IsPrime.ne_top hP₁
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective hP₃ hP₂)
  rwa [Nat.card_units] at h

/--
If the prime ideal `P` is unramified over `ℤ` and the norm of the prime of `ℤ` lying under `P` is
different from `2`, then the norm of `P` is congruent to `1` modulo `torsionOrder K`.

See `NumberField.torsionOrder_dvd_absNorm_sub_one` for a version where, instead, the norm of `P` is
assumed coprime with `torsionOrder K`.
-/
theorem NumberField.torsionOrder_dvd_absNorm_sub_one' {P : Ideal (𝓞 K)} [hP : P.IsPrime]
    (hP₁ : Algebra.IsUnramifiedAt ℤ P) (hP₂ : absNorm (under ℤ P) ≠ 2) :
    torsionOrder K ∣ absNorm P - 1 := by
  obtain hP₂ | hP₂ := Nat.lt_or_gt.mp hP₂
  · obtain hP₂ | hP₂ := Nat.lt_succ_iff_lt_or_eq.mp hP₂
    · have : P.LiesOver (⊥ : Ideal ℤ) := by
        rwa [liesOver_iff, eq_comm, ← absNorm_eq_zero_iff, ← Nat.lt_one_iff]
      rw [eq_bot_of_liesOver_bot ℤ P, absNorm_bot, Nat.zero_sub_one]
      exact Nat.dvd_zero _
    · rw [absNorm_eq_one_iff, comap_eq_top_iff, ← absNorm_eq_one_iff] at hP₂
      simp [hP₂]
  have hP₀ : P ≠ ⊥ := fun h ↦ by simp [h] at hP₂
  have : P.IsMaximal := Ring.DimensionLEOne.maximalOfPrime hP₀ hP
  let _ := Ideal.Quotient.field P
  have h := Subgroup.card_dvd_of_injective _ (torsionMapQuot_injective' hP₁ hP₂)
  rwa [Nat.card_units] at h

end torsionMapQuot

instance [NumberField K] [I.IsMaximal] : Finite (𝓞 K ⧸ I) :=
  I.finiteQuotientOfFreeOfNeBot (I.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'

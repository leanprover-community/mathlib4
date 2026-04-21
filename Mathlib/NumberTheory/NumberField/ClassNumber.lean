/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Riccardo Brasca, Xavier Roblot
-/
module

public import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
public import Mathlib.NumberTheory.ClassNumber.Finite
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.NumberTheory.RamificationInertia.Galois

/-!
# Class numbers of number fields

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
We denote by `M K` the Minkowski bound of a number field `K`, defined as
`(4 / π) ^ nrComplexPlaces K * ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)`.
- `NumberField.classNumber`: the class number of a number field is the (finite)
  cardinality of the class group of its ring of integers
- `isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc`: let `K`
  be a number field. To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
  `p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, all ideals `P` above `p` such that
  `p ^ (span ({p}).inertiaDeg P) ≤ ⌊(M K)⌋₊` are principal. This is the standard technique to prove
  that `𝓞 K` is principal, see [marcus1977number], discussion after Theorem 37.
  The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
  to deal with the finite number of primes `p` in the interval.
- `isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`: let `K`
  be a number field such that `K/ℚ` is Galois. To show that `𝓞 K` is a PID it is enough to show
  that, for all (natural) primes `p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, there is an ideal `P` above `p` such
  that either `⌊(M K)⌋₊ < p ^ (span ({p}).inertiaDeg P)` or `P` is principal. This is the standard
  technique to prove that `𝓞 K` is principal in the Galois case, see [marcus1977number], discussion
  after Theorem 37.
  The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
  to deal with the finite number of primes `p` in the interval.
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

open scoped nonZeroDivisors Real

open Module NumberField InfinitePlace Ideal Nat

variable (K : Type*) [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|)

namespace NumberField

namespace RingOfIntegers

noncomputable instance instFintypeClassGroup : Fintype (ClassGroup (𝓞 K)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ K AbsoluteValue.absIsAdmissible

end RingOfIntegers

/-- The class number of a number field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (𝓞 K))

theorem classNumber_ne_zero : classNumber K ≠ 0 := Fintype.card_ne_zero

theorem classNumber_pos : 0 < classNumber K := Fintype.card_pos

variable {K}

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  card_classGroup_eq_one_iff

theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      absNorm (I : Ideal (𝓞 K)) ≤ M K := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := dvd_iff_le.mpr ((span_singleton_le_iff_mem J).mpr (by exact ha))
  have : I₀ ≠ 0 := by
    contrapose h_nz
    rw [h_nz, mul_zero, zero_eq_bot, span_singleton_eq_bot] at hI
    rw [Algebra.linearMap_apply, hI, map_zero]
  let I := (⟨I₀, mem_nonZeroDivisors_iff_ne_zero.mpr this⟩ : (Ideal (𝓞 K))⁰)
  refine ⟨I, ?_, ?_⟩
  · suffices ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ by rw [this, hJ, inv_inv]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨a, Subtype.coe_ne_coe.1 h_nz, by rw [mul_comm, hI]⟩
  · rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), Algebra.linearMap_apply,
      ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_absNorm, hI, map_mul,
      cast_mul, Rat.cast_mul, absNorm_apply, Rat.cast_natCast, Rat.cast_natCast,
      FractionalIdeal.coe_mk0, FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, mul_div_assoc,
      mul_assoc, mul_assoc] at h_nm
    refine le_of_mul_le_mul_of_pos_left h_nm ?_
    exact cast_pos.mpr <| pos_of_ne_zero <| absNorm_ne_zero_of_nonZeroDivisors J

end NumberField

namespace RingOfIntegers

variable {K}

open scoped NumberField

theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, absNorm (I : Ideal (𝓞 K)) ≤ M K →
      Submodule.IsPrincipal (I : Ideal (𝓞 K))) : IsPrincipalIdealRing (𝓞 K) := by
  rw [← classNumber_eq_one_iff, classNumber, Fintype.card_eq_one_iff]
  refine ⟨1, fun C ↦ ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  simpa [← ClassGroup.mk0_eq_one_iff] using h hI

theorem isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime
    (h : ∀ ⦃I : (Ideal (𝓞 K))⁰⦄, (I : Ideal (𝓞 K)).IsPrime →
      absNorm (I : Ideal (𝓞 K)) ≤ M K → Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI ↦ ?_)
  rw [← mem_isPrincipalSubmonoid_iff,
    ← Ideal.prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ ↦ mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J = 0
  · simpa [hJ0] using bot_isPrincipal
  rw [← Subtype.coe_mk J (mem_nonZeroDivisors_of_ne_zero hJ0)]
  refine h (((mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mp hJ).1) ?_
  exact (cast_le.mpr <| le_of_dvd (absNorm_pos_of_nonZeroDivisors I) <|
    absNorm_dvd_absNorm_of_le <| le_of_dvd <|
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hJ).trans hI

set_option linter.style.longLine false in
/-- Let `K` be a number field and let `M K` be the Minkowski bound of `K`.
To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
`p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, all ideals `P` above `p` such that
`p ^ (span ({p}).inertiaDeg P) ≤ ⌊(M K)⌋₊` are principal. This is the standard technique to prove
that `𝓞 K` is principal, see [marcus1977number], discussion after Theorem 37.
If `K/ℚ` is Galois, one can use the more convenient
`RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc`
below.

The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
to deal with the finite number of primes `p` in the interval. -/
theorem isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime → ∀ (P : Ideal (𝓞 K)),
      P ∈ primesOver (span {(p : ℤ)}) (𝓞 K) → p ^ ((span ({↑p} : Set ℤ)).inertiaDeg P) ≤ ⌊(M K)⌋₊ →
      Submodule.IsPrincipal P) : IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_isPrime <|
    fun ⟨P, HP⟩ hP hPN ↦ ?_
  obtain ⟨p, hp⟩ := IsPrincipalIdealRing.principal <| under ℤ P
  have hp0 : p ≠ 0 := fun h ↦ nonZeroDivisors.coe_ne_zero ⟨P, HP⟩ <|
    eq_bot_of_comap_eq_bot (R := ℤ) <| by simpa only [hp, submodule_span_eq, span_singleton_eq_bot]
  have hpprime := (span_singleton_prime hp0).mp
  simp only [← submodule_span_eq, ← hp] at hpprime
  have hlies : P.LiesOver (span {p}) := by
    rcases abs_choice p with h | h <;>
    simpa [h, span_singleton_neg p, ← submodule_span_eq, ← hp] using over_under P
  have hspan : span {↑p.natAbs} = span {p} := by
    rcases abs_choice p with h | h <;> simp [h]
  have hple : p.natAbs ^ (span {(p.natAbs : ℤ)}).inertiaDeg P ≤ ⌊(M K)⌋₊ := by
    refine le_floor ?_
    simpa only [hspan, ← cast_pow, ← absNorm_eq_pow_inertiaDeg P (hpprime (hP.under _))] using hPN
  have hpabsprime := Int.prime_iff_natAbs_prime.mp (hpprime (hP.under _))
  refine h _ ?_ hpabsprime _ ⟨hP, ?_⟩ hple
  · suffices 0 < (span {(p.natAbs : ℤ)}).inertiaDeg P by
      exact Finset.mem_Icc.mpr ⟨hpabsprime.one_le, le_trans (le_pow this) hple⟩
    have := (isPrime_of_prime (prime_span_singleton_iff.mpr <|
      hpprime (hP.under _))).isMaximal <| by simp [((hpprime (hP.under _))).ne_zero]
    exact hspan ▸ inertiaDeg_pos ..
  · exact hspan ▸ hlies

/-- Let `K` be a number field such that `K/ℚ` is Galois and let `M K` be the Minkowski bound of `K`.
To show that `𝓞 K` is a PID it is enough to show that, for all (natural) primes
`p ∈ Finset.Icc 1 ⌊(M K)⌋₊`, there is an ideal `P` above `p` such that
either `⌊(M K)⌋₊ < p ^ (span ({p}).inertiaDeg P)` or `P` is principal. This is the standard
technique to prove that `𝓞 K` is principal in the Galois case, see [marcus1977number], discussion
after Theorem 37.

The way this theorem should be used is to first compute `⌊(M K)⌋₊` and then to use `fin_cases`
to deal with the finite number of primes `p` in the interval. -/
theorem isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    [IsGalois ℚ K] (h : ∀ p ∈ Finset.Icc 1 ⌊(M K)⌋₊, p.Prime →
      ∃ P ∈ primesOver (span {(p : ℤ)}) (𝓞 K),
        ⌊(M K)⌋₊ < p ^ ((span ({↑p} : Set ℤ)).inertiaDeg P) ∨
          Submodule.IsPrincipal P) :
      IsPrincipalIdealRing (𝓞 K) := by
  refine isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
    (fun p hpmem hp P ⟨hP1, hP2⟩ hple ↦ ?_)
  obtain ⟨Q, ⟨hQ1, hQ2⟩, H⟩ := h p hpmem hp
  have := (isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hp))).isMaximal
    (by simp [hp.ne_zero])
  by_cases h : ⌊(M K)⌋₊ < p ^ ((span ({↑p} : Set ℤ)).inertiaDeg P)
  · linarith
  rw [inertiaDeg_eq_of_isGaloisGroup _ Q P (K ≃ₐ[ℚ] K)] at H
  obtain ⟨σ, rfl⟩ := exists_smul_eq_of_isGaloisGroup (span ({↑p} : Set ℤ)) Q P (K ≃ₐ[ℚ] K)
  exact (H.resolve_left h).map_ringHom (MulSemiringAction.toRingHom (K ≃ₐ[ℚ] K) (𝓞 K) σ)

theorem isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  have : 0 < finrank ℚ K := finrank_pos -- Lean needs to know this for `positivity` to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity), mul_assoc, ← inv_mul_lt_iff₀' (by positivity),
    mul_inv, ← inv_pow, inv_div, inv_div, mul_assoc, Int.cast_abs] at h
  refine isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI ↦ ?_)
  rw [absNorm_eq_one_iff.mp <| le_antisymm (Nat.lt_succ_iff.mp (cast_lt.mp
    (lt_of_le_of_lt hI h))) <| one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors I)]
  exact top_isPrincipal

end RingOfIntegers

namespace Rat

open NumberField

theorem classNumber_eq : NumberField.classNumber ℚ = 1 :=
  classNumber_eq_one_iff.mpr <| IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective

end Rat

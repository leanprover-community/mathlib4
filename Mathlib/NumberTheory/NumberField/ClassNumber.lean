/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.RingTheory.Ideal.IsPrincipal

/-!
# Class numbers of number fields

This file defines the class number of a number field as the (finite) cardinality of
the class group of its ring of integers. It also proves some elementary results
on the class number.

## Main definitions
- `NumberField.classNumber`: the class number of a number field is the (finite)
cardinality of the class group of its ring of integers
-/

namespace NumberField

variable (K : Type*) [Field K] [NumberField K]

namespace RingOfIntegers

noncomputable instance instFintypeClassGroup : Fintype (ClassGroup (𝓞 K)) :=
  ClassGroup.fintypeOfAdmissibleOfFinite ℚ K AbsoluteValue.absIsAdmissible

end RingOfIntegers

/-- The class number of a number field is the (finite) cardinality of the class group. -/
noncomputable def classNumber : ℕ :=
  Fintype.card (ClassGroup (𝓞 K))

variable {K}

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  card_classGroup_eq_one_iff

open Module NumberField.InfinitePlace Ideal Nat

open scoped nonZeroDivisors Real

theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      absNorm (I : Ideal (𝓞 K)) ≤ (4 / π) ^ nrComplexPlaces K *
        ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := dvd_iff_le.mpr ((span_singleton_le_iff_mem J).mpr (by exact ha))
  have : I₀ ≠ 0 := by
    contrapose! h_nz
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

theorem _root_.RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le
    (h : ∀ I : (Ideal (𝓞 K))⁰, absNorm (I : Ideal (𝓞 K)) ≤ (4 / π) ^ nrComplexPlaces K *
        ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|) →
        Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  rw [← classNumber_eq_one_iff, classNumber, Fintype.card_eq_one_iff]
  refine ⟨1, fun C ↦ ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  simpa [← ClassGroup.mk0_eq_one_iff] using h _ hI

theorem _root_.RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le_of_prime
    (h : ∀ (I : (Ideal (𝓞 K))⁰), (I : Ideal (𝓞 K)).IsPrime →
      absNorm (I : Ideal (𝓞 K)) ≤ (4 / π) ^ nrComplexPlaces K *
        ((finrank ℚ K)! / (finrank ℚ K) ^ (finrank ℚ K) * √|discr K|) →
      Submodule.IsPrincipal (I : Ideal (𝓞 K))) :
    IsPrincipalIdealRing (𝓞 K) := by
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI ↦ ?_)
  rw [← mem_isPrincipalSubmonoid_iff,
    ← prod_normalizedFactors_eq_self (nonZeroDivisors.coe_ne_zero I)]
  refine Submonoid.multiset_prod_mem _ _ (fun J hJ ↦ mem_isPrincipalSubmonoid_iff.mp ?_)
  by_cases hJ0 : J = 0
  · simpa [hJ0] using bot_isPrincipal
  rw [← Subtype.coe_mk J (mem_nonZeroDivisors_of_ne_zero hJ0)]
  refine h _ ?_ ?_
  · exact ((mem_normalizedFactors_iff (nonZeroDivisors.coe_ne_zero I)).mp hJ).1
  · exact (cast_le.mpr <| le_of_dvd (absNorm_pos_of_nonZeroDivisors I) <|
      absNorm_dvd_absNorm_of_le (le_of_dvd (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
      hJ))).trans hI

theorem _root_.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ nrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K)!)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  have : 0 < finrank ℚ K := finrank_pos -- Lean needs to know that for positivity to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity), mul_assoc, ← inv_mul_lt_iff₀' (by positivity),
    mul_inv, ← inv_pow, inv_div, inv_div, mul_assoc, Int.cast_abs] at h
  refine RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_norm_le (fun I hI ↦ ?_)
  convert top_isPrincipal
  exact absNorm_eq_one_iff.mp <| le_antisymm (lt_succ.mp (cast_lt.mp
    (lt_of_le_of_lt hI h))) <| one_le_iff_ne_zero.mpr (absNorm_ne_zero_of_nonZeroDivisors I)

end NumberField

namespace Rat

open NumberField

theorem classNumber_eq : NumberField.classNumber ℚ = 1 :=
  classNumber_eq_one_iff.mpr <| IsPrincipalIdealRing.of_surjective
    Rat.ringOfIntegersEquiv.symm Rat.ringOfIntegersEquiv.symm.surjective

end Rat

/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import Mathlib.NumberTheory.ClassNumber.AdmissibleAbs
import Mathlib.NumberTheory.ClassNumber.Finite
import Mathlib.NumberTheory.NumberField.Discriminant

#align_import number_theory.number_field.class_number from "leanprover-community/mathlib"@"d0259b01c82eed3f50390a60404c63faf9e60b1f"

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
#align number_field.class_number NumberField.classNumber

variable {K}

/-- The class number of a number field is `1` iff the ring of integers is a PID. -/
theorem classNumber_eq_one_iff : classNumber K = 1 ↔ IsPrincipalIdealRing (𝓞 K) :=
  card_classGroup_eq_one_iff
#align number_field.class_number_eq_one_iff NumberField.classNumber_eq_one_iff

open FiniteDimensional NumberField.InfinitePlace

open scoped nonZeroDivisors Real

theorem exists_ideal_in_class_of_norm_le (C : ClassGroup (𝓞 K)) :
    ∃ I : (Ideal (𝓞 K))⁰, ClassGroup.mk0 I = C ∧
      Ideal.absNorm (I : Ideal (𝓞 K)) ≤ (4 / π) ^ NrComplexPlaces K *
        ((finrank ℚ K).factorial / (finrank ℚ K) ^ (finrank ℚ K) * Real.sqrt |discr K|) := by
  obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨_, ⟨a, ha, rfl⟩, h_nz, h_nm⟩ :=
    exists_ne_zero_mem_ideal_of_norm_le_mul_sqrt_discr K (FractionalIdeal.mk0 K J)
  obtain ⟨I₀, hI⟩ := Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem J).mpr (by convert ha))
  have : I₀ ≠ 0 := by
    contrapose! h_nz
    rw [h_nz, mul_zero, show 0 = (⊥ : Ideal (𝓞 K)) by rfl, Ideal.span_singleton_eq_bot] at hI
    rw [Algebra.linearMap_apply, hI, map_zero]
  let I := (⟨I₀, mem_nonZeroDivisors_iff_ne_zero.mpr this⟩ : (Ideal (𝓞 K))⁰)
  refine ⟨I, ?_, ?_⟩
  · suffices ClassGroup.mk0 I = (ClassGroup.mk0 J)⁻¹ by rw [this, hJ, inv_inv]
    exact ClassGroup.mk0_eq_mk0_inv_iff.mpr ⟨a, Subtype.coe_ne_coe.1 h_nz, by rw [mul_comm, hI]⟩
  · rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), Algebra.linearMap_apply,
      ← FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_absNorm, hI, map_mul,
      Nat.cast_mul, Rat.cast_mul, show Ideal.absNorm I₀ = Ideal.absNorm (I : Ideal (𝓞 K)) by rfl,
      Rat.cast_natCast, Rat.cast_natCast, FractionalIdeal.coe_mk0,
      FractionalIdeal.coeIdeal_absNorm, Rat.cast_natCast, mul_div_assoc, mul_assoc, mul_assoc]
      at h_nm
    refine le_of_mul_le_mul_of_pos_left h_nm ?_
    exact Nat.cast_pos.mpr <| Nat.pos_of_ne_zero <| Ideal.absNorm_ne_zero_of_nonZeroDivisors J

theorem _root_.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
    (h : |discr K| < (2 * (π / 4) ^ NrComplexPlaces K *
      ((finrank ℚ K) ^ (finrank ℚ K) / (finrank ℚ K).factorial)) ^ 2) :
    IsPrincipalIdealRing (𝓞 K) := by
  have : 0 < finrank ℚ K := finrank_pos -- Lean needs to know that for positivity to succeed
  rw [← Real.sqrt_lt (by positivity) (by positivity), mul_assoc, ← inv_mul_lt_iff' (by positivity),
    mul_inv, ← inv_pow, inv_div, inv_div, mul_assoc, Int.cast_abs] at h
  rw [← classNumber_eq_one_iff, classNumber, Fintype.card_eq_one_iff]
  refine ⟨1, fun C ↦ ?_⟩
  obtain ⟨I, rfl, hI⟩ := exists_ideal_in_class_of_norm_le C
  have : Ideal.absNorm I.1 = 1 := by
    refine le_antisymm (Nat.lt_succ.mp ?_) (Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_ne_zero_of_nonZeroDivisors I))
    exact Nat.cast_lt.mp <| lt_of_le_of_lt hI h
  rw [ClassGroup.mk0_eq_one_iff, Ideal.absNorm_eq_one_iff.mp this]
  exact top_isPrincipal

end NumberField

namespace Rat

open NumberField

theorem classNumber_eq : NumberField.classNumber ℚ = 1 :=
  classNumber_eq_one_iff.mpr <| by
    convert IsPrincipalIdealRing.of_surjective
      (Rat.ringOfIntegersEquiv.symm: ℤ →+* 𝓞 ℚ) Rat.ringOfIntegersEquiv.symm.surjective
#align rat.class_number_eq Rat.classNumber_eq

end Rat

/-
Copyright (c) 2025 Ruben Van de Velde. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ruben Van de Velde
-/

import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Localization.NumDen

/-!
# Ring-theoretic fractions in ℚ
-/

namespace Rat

theorem isLocalizationIsInteger_iff (q : ℚ) :
    IsLocalization.IsInteger ℤ q ↔ q ∈ Set.range Int.cast := by
  simp [IsLocalization.IsInteger]

theorem isFractionRingDen (q : ℚ) : (IsFractionRing.den ℤ q : ℤ).natAbs = q.den := by
  conv_rhs => rw [← IsFractionRing.mk'_num_den ℤ q]
  simp only [IsFractionRing.mk'_eq_div, algebraMap_int_eq, eq_intCast]
  apply Nat.cast_injective (R := ℤ)
  have := IsFractionRing.num_den_reduced ℤ q
  rw [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] at this
  obtain h | h | h := lt_trichotomy (IsFractionRing.den ℤ q : ℤ) 0
  · have h_pos : 0 < -(IsFractionRing.den ℤ q : ℤ) := neg_pos_of_neg h
    rw [Int.ofNat_natAbs_of_nonpos h.le, ← neg_div_neg_eq, ← Int.cast_neg, ← Int.cast_neg]
    rw [Rat.den_div_eq_of_coprime h_pos (by rwa [Int.natAbs_neg, Int.natAbs_neg])]
  · simp at h
  · rw [Rat.den_div_eq_of_coprime h this, Int.natAbs_of_nonneg h.le]

theorem isFractionRingNum (q : ℚ) : Associated (IsFractionRing.num ℤ q : ℤ) q.num := by
  conv_rhs => rw [← IsFractionRing.mk'_num_den ℤ q]
  simp only [IsFractionRing.mk'_eq_div, algebraMap_int_eq, eq_intCast]
  have := IsFractionRing.num_den_reduced ℤ q
  rw [isRelPrime_iff_isCoprime, Int.isCoprime_iff_nat_coprime] at this
  obtain h | h | h := lt_trichotomy (IsFractionRing.den ℤ q : ℤ) 0
  · have h_pos : 0 < -(IsFractionRing.den ℤ q : ℤ) := neg_pos_of_neg h
    rw [← neg_div_neg_eq, ← Int.cast_neg, ← Int.cast_neg]
    rw [Rat.num_div_eq_of_coprime h_pos (by rwa [Int.natAbs_neg, Int.natAbs_neg]),
      Associated.neg_right_iff]
  · simp at h
  · rw [Rat.num_div_eq_of_coprime h this]

end Rat

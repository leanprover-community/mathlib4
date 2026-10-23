/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.NormNum.Prime

/-!
# Cyclotomic fields whose ring of integers is a PID.

We prove that `ℤ [ζₚ]` is a PID for specific values of `p`. The result holds for `p ≤ 19`,
but the proof is more and more involved.

## Main results
* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
* `seven_pid`: If `IsCyclotomicExtension {7} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

public section

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Polynomial InfinitePlace Nat Real cyclotomic RingOfIntegers Ideal

variable (K : Type u) [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((Module.finrank ℚ K)! / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) * √|NumberField.discr K|)

/-- If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K
    (irreducible_rat (by simp)), nrComplexPlaces_eq_totient_div_two 3, totient_prime
      Nat.prime_three]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, zero_lt_two, Nat.div_self, pow_one,
    cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (zero_lt_three' ℝ), factorial_two]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/-- If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem five_pid [IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [discr_prime 5 K, IsCyclotomicExtension.finrank (n := 5) K
    (irreducible_rat (by simp)), nrComplexPlaces_eq_totient_div_two 5,
    totient_prime Nat.prime_five]
  simp only [Int.reduceNeg, succ_sub_succ_eq_sub, tsub_zero, reduceDiv, even_two, Even.neg_pow,
    one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs, Int.cast_ofNat,
    abs_of_pos (show (0 : ℝ) < 125 by simp), div_pow, show 4! = 24 by rfl]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 from
    lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/-- If `IsCyclotomicExtension {7} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem seven_pid [IsCyclotomicExtension {7} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {7} ℚ K
  -- The Minkowski bound is `4`.
  have hM : ⌊(M K)⌋₊ = 4 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    rw [discr_prime 7 K, IsCyclotomicExtension.finrank (n := 7) K (irreducible_rat (by simp)),
      nrComplexPlaces_eq_totient_div_two 7, totient_prime Nat.prime_seven]
    simp only [Nat.add_one_sub_one, reduceDiv, cast_ofNat, Int.reduceNeg, Int.reducePow,
      reduceSub, neg_mul, one_mul, Int.cast_neg, Int.cast_ofNat, abs_neg, abs_ofNat]
    refine (floor_eq_iff (by positivity)).mpr ⟨?_, ?_⟩
    · calc
        (4 : ℝ) ≤ (4 / 3.15) ^ 3 * (6! / 6 ^ 6 * 129) := by norm_num
        _ ≤ (4 / π) ^ 3 * (6! / 6 ^ 6 * √16807) := by
          gcongr
          · exact pi_lt_d2.le
          · exact (le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    · calc
        (4 / π) ^ 3 * (6! / 6 ^ 6 * √16807) ≤ (4 / 3) ^ 3 * (6! / 6 ^ 6 * 130) := by
          gcongr
          · exact pi_gt_three.le
          · exact (sqrt_le_left (by norm_num)).mpr (by norm_num)
        _ < _ := by norm_num
  refine isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    fun p hp hprime ↦ ?_
  have : (span {(p : ℤ)}).IsPrime :=
    isPrime_of_prime (prime_span_singleton_iff.mpr (prime_iff_prime_int.mp hprime))
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, ⟨‹_›, ‹_›⟩, Or.inl ?_⟩
  rw [hM] at hp ⊢
  obtain ⟨h₁, h₄⟩ := Finset.mem_Icc.mp hp
  interval_cases p
  · norm_num at hprime
  · have h : orderOf (2 : ZMod 7) = 3 := (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
    rw [inertiaDeg_eq_of_not_dvd (m := 7) 2 K P (by norm_num)]
    norm_num [h]
  · have h : orderOf (3 : ZMod 7) = 6 := (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
    rw [inertiaDeg_eq_of_not_dvd (m := 7) 3 K P (by norm_num)]
    norm_num [h]
  · norm_num at hprime

end IsCyclotomicExtension.Rat

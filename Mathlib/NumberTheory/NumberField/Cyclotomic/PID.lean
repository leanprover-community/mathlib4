/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Embeddings

meta import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Sqrt
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Tactic

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

open NumberField Polynomial InfinitePlace Nat Real cyclotomic NumberField.RingOfIntegers Ideal

variable (K : Type u) [Field K] [NumberField K]

local notation "M " K:70 => (4 / π) ^ nrComplexPlaces K *
  ((Module.finrank ℚ K)! / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) * √|NumberField.discr K|)

/-- If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem three_pid [IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  apply NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
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
  apply NumberField.RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
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
  have : IsGalois ℚ K := isGalois {7} ℚ K
  -- The Minkowski bound is `4`.
  have hM : ⌊(M K)⌋₊ = 4 := by
    have : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
    have : π ∈ Set.Ioo 3 3.15 := ⟨pi_gt_three, pi_lt_d2⟩
    rw [floor_eq_iff (by positivity), discr_prime 7 K, finrank 7 K,
      nrComplexPlaces_eq_totient_div_two 7, totient_prime Nat.prime_seven]
    norm_num
    field_simp
    dyadic_interval [prec := 5]
  refine isPrincipalIdealRing_of_isPrincipal_of_lt_or_isPrincipal_of_mem_primesOver_of_mem_Icc
    fun p hp hprime ↦ ?_
  have : Fact p.Prime := ⟨hprime⟩
  obtain ⟨⟨P, _, _⟩⟩ := (span {(p : ℤ)}).nonempty_primesOver (S := 𝓞 K)
  refine ⟨P, ⟨‹_›, ‹_›⟩, Or.inl ?_⟩
  rw [hM] at hp ⊢
  fin_cases hp <;> try exact absurd hprime (by decide)
  · rw [inertiaDeg_eq_of_not_dvd (m := 7) 2 K P (by decide),
      (orderOf_eq_iff (n := 3) (by decide)).mpr ⟨by decide, by decide⟩]
    decide
  · rw [inertiaDeg_eq_of_not_dvd (m := 7) 3 K P (by decide),
      (orderOf_eq_iff (n := 6) (by decide)).mpr ⟨by decide, by decide⟩]
    decide

end IsCyclotomicExtension.Rat

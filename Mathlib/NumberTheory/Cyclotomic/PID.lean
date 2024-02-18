/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.NumberTheory.Cyclotomic.Embeddings

/-!
# Cyclotomic fields that are PID.
We prove that `𝓞 ℚ(ζₚ)` is a PID for specific values of `p`. The result holds for `p ≤ 19`,
but the proof is more and more involved.

## Main results
* `three_pid`: If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain.
* `five_pid`: If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain.
-/

universe u

namespace IsCyclotomicExtension.Rat

open NumberField Polynomial InfinitePlace Nat Real

variable (K : Type u) [Field K] [NumberField K]

/-- If `IsCyclotomicExtension {3} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem three_pid [h : IsCyclotomicExtension {3} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have hpos : 0 < 3 := by norm_num
  have hp : Fact (Nat.Prime ((3 : ℕ+) : ℕ)) := ⟨Nat.prime_three⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [absdiscr_prime 3 K, IsCyclotomicExtension.finrank (n := 3) K
    (cyclotomic.irreducible_rat hpos), nrComplexPlaces_eq_totient_div_two 3, totient_prime hp.1]
  simp only [Int.reduceNeg, show ((3 : ℕ+) : ℕ) = 3 by rfl, succ_sub_succ_eq_sub, tsub_zero,
    zero_lt_two, Nat.div_self, pow_one, cast_ofNat, neg_mul, one_mul, abs_neg, Int.cast_abs,
    Int.int_cast_ofNat, factorial_two, gt_iff_lt, abs_of_pos (show (0 : ℝ) < 3 from by norm_num)]
  suffices (2 * (3 / 4) * (2 ^ 2 / 2)) ^ 2 < (2 * (π / 4) * (2 ^ 2 / 2)) ^ 2 by
    exact lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

/-- If `IsCyclotomicExtension {5} ℚ K` then `𝓞 K` is a principal ideal domain. -/
theorem five_pid [h : IsCyclotomicExtension {5} ℚ K] : IsPrincipalIdealRing (𝓞 K) := by
  have hpos : 0 < 5 := by norm_num
  have hp : Fact (Nat.Prime ((5 : ℕ+) : ℕ)) := ⟨by decide⟩
  apply RingOfIntegers.isPrincipalIdealRing_of_abs_discr_lt
  rw [absdiscr_prime 5 K, IsCyclotomicExtension.finrank (n := 5) K
    (cyclotomic.irreducible_rat hpos), nrComplexPlaces_eq_totient_div_two 5, totient_prime hp.1]
  simp only [Int.reduceNeg, show ((5 : ℕ+) : ℕ) = 5 by rfl, succ_sub_succ_eq_sub, tsub_zero,
    reduceDiv, even_two, Even.neg_pow, one_pow, cast_ofNat, Int.reducePow, one_mul, Int.cast_abs,
    Int.int_cast_ofNat, div_pow, gt_iff_lt, show 4! = 24 by rfl, abs_of_pos
    (show (0 : ℝ) < 125 from by norm_num)]
  suffices (2 * (3 ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 < (2 * (π ^ 2 / 4 ^ 2) * (4 ^ 4 / 24)) ^ 2 by
    exact lt_trans (by norm_num) this
  gcongr
  exact pi_gt_three

end IsCyclotomicExtension.Rat

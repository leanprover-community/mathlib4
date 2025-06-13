/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic

/-!
# Cyclotomic extensions of `ℚ` are totally complex number fields.
We prove that cyclotomic extensions of `ℚ` are totally complex, meaning that
`NrRealPlaces K = 0` if `IsCyclotomicExtension {n} ℚ K` and `2 < n`.

## Main results
* `nrRealPlaces_eq_zero`: If `K` is a `n`-th cyclotomic extension of `ℚ`, where `2 < n`,
  then there are no real places of `K`.
-/

universe u

namespace IsCyclotomicExtension.Rat

open NumberField InfinitePlace Module Complex Nat Polynomial

variable {n : ℕ} [NeZero n] (K : Type u) [Field K] [CharZero K]

/-- If `K` is a `n`-th cyclotomic extension of `ℚ`, where `2 < n`, then there are no real places
of `K`. -/
theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K]
    (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    nrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  apply (IsCyclotomicExtension.zeta_spec n ℚ K).nrRealPlaces_eq_zero_of_two_lt hn

variable (n)

/-- If `K` is a `n`-th cyclotomic extension of `ℚ`, then there are `φ n / n` complex places
of `K`. Note that this uses `1 / 2 = 0` in the cases `n = 1, 2`. -/
theorem nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    nrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn, zero_add, IsCyclotomicExtension.finrank (n := n) K
      (cyclotomic.irreducible_rat (NeZero.pos _)), hk, ← two_mul,
      Nat.mul_right_inj (by norm_num)] at key
    simp [hk, key, ← two_mul]
  · have : φ n = 1 := by
      by_cases h1 : 1 < n
      · convert totient_two
        exact (eq_of_le_of_not_lt (succ_le_of_lt h1) hn).symm
      · convert totient_one
        exact eq_of_le_of_not_lt (not_lt.mp h1) (by simp [NeZero.ne _])
    rw [this]
    apply nrComplexPlaces_eq_zero_of_finrank_eq_one
    rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat (NeZero.pos n)), this]


end IsCyclotomicExtension.Rat

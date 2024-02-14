/-
Copyright (c) 2024 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Embeddings

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

open NumberField InfinitePlace FiniteDimensional Complex Nat Polynomial

variable {n : ℕ+} (K : Type u) [Field K] [CharZero K]

theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K]
    (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    NrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  apply (IsCyclotomicExtension.zeta_spec n ℚ K).nrRealPlaces_eq_zero_of_two_lt hn

theorem nrComplexPlaces_eq_totient_div_two [h : IsCyclotomicExtension {n} ℚ K] :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    NrComplexPlaces K = φ n / 2 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  by_cases hn : 2 < n
  · obtain ⟨k, hk : φ n = k + k⟩ := totient_even hn
    have key := card_add_two_mul_card_eq_rank K
    rw [nrRealPlaces_eq_zero K hn, zero_add, IsCyclotomicExtension.finrank (n := n) K
      (cyclotomic.irreducible_rat n.pos), hk, ← two_mul, Nat.mul_right_inj (by norm_num)] at key
    simp [hk, key, ← two_mul]
  · have : n.1 = 0 ∨ n.1 = 1 ∨ n.1 = 2 := by
      suffices n.1 ≤ 2 by
        omega
      exact not_lt.1 hn
    rcases this with (h0 | h1 | h2)
    · exfalso
      exact n.2.ne' h0
    · simp only [PNat.coe_eq_one_iff.1 h1, PNat.one_coe, totient_one, reduceDiv]
      apply nrComplexPlaces_eq_zero_of_finrank_eq_one
      rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat n.pos)]
      convert totient_one
    · have h2' : n = 2 := by
        rw [← PNat.coe_inj]
        exact h2
      simp only [h2', show ((2 : ℕ+) : ℕ) = 2 from rfl, totient_two, reduceDiv]
      apply nrComplexPlaces_eq_zero_of_finrank_eq_one
      rw [IsCyclotomicExtension.finrank K (cyclotomic.irreducible_rat n.pos)]
      convert totient_two


end IsCyclotomicExtension.Rat

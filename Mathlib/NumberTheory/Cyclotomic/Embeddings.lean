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
`NrRealPlaces K = 0` if `IsCyclotomicExtension {p ^ (k + 1)} ℚ K` and `p` is odd.

## Main results
* `nrRealPlaces_eq_zero_odd_prime_pow`: If `K` is a `p ^ (k + 1)` cyclotomic extension of
`ℚ`, where `p` is an odd prime, then there are no real places of `K`.
-/

universe u

namespace IsCyclotomicExtension.Rat

open NumberField InfinitePlace FiniteDimensional Complex Nat

open scoped Cyclotomic

variable {p : ℕ+} (k : ℕ) (K : Type u) [Field K] [CharZero K] [hp : Fact (p : ℕ).Prime]

theorem nrRealPlaces_eq_zero_odd_prime_pow [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hodd : p ≠ 2) :
    haveI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
    NrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  apply (IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K).nrRealPlaces_eq_zero_of_two_lt
  refine lt_of_lt_of_le (lt_of_le_of_ne hp.1.two_le (fun h ↦ hodd (PNat.coe_inj.1 ?_)))
    <| le_self_pow hp.1.one_lt.le (succ_ne_zero k)
  rw [← h]
  rfl

theorem nrRealPlaces_eq_zero_odd_prime [IsCyclotomicExtension {p} ℚ K]
    (hodd : p ≠ 2) :
    haveI := IsCyclotomicExtension.numberField {p} ℚ K
    NrRealPlaces K = 0 := by
  have : IsCyclotomicExtension {p ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
  exact nrRealPlaces_eq_zero_odd_prime_pow 0 K hodd

theorem nrComplexPlaces_eq_finrank_odd_prime_pow [IsCyclotomicExtension {p ^ (k + 1)} ℚ K]
    (hodd : p ≠ 2) :
    haveI := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
    2 * NrComplexPlaces K = FiniteDimensional.finrank ℚ K := by
  have := IsCyclotomicExtension.numberField {p ^ (k + 1)} ℚ K
  simpa [nrRealPlaces_eq_zero_odd_prime_pow k K hodd] using card_add_two_mul_card_eq_rank K

theorem nrComplexPlaces_eq_finrank_odd_prime [IsCyclotomicExtension {p} ℚ K]
    (hodd : p ≠ 2) :
    haveI := IsCyclotomicExtension.numberField {p} ℚ K
    2 * NrComplexPlaces K = FiniteDimensional.finrank ℚ K := by
  have := IsCyclotomicExtension.numberField {p} ℚ K
  simpa [nrRealPlaces_eq_zero_odd_prime K hodd] using card_add_two_mul_card_eq_rank K

end IsCyclotomicExtension.Rat

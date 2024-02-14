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

variable {n : ℕ+} (K : Type u) [Field K] [CharZero K]

theorem nrRealPlaces_eq_zero [IsCyclotomicExtension {n} ℚ K]
    (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    NrRealPlaces K = 0 := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  apply (IsCyclotomicExtension.zeta_spec n ℚ K).nrRealPlaces_eq_zero_of_two_lt hn

theorem nrComplexPlaces_eq_finrank [IsCyclotomicExtension {n} ℚ K]
    (hn : 2 < n) :
    haveI := IsCyclotomicExtension.numberField {n} ℚ K
    2 * NrComplexPlaces K = FiniteDimensional.finrank ℚ K := by
  have := IsCyclotomicExtension.numberField {n} ℚ K
  simpa [nrRealPlaces_eq_zero K hn] using card_add_two_mul_card_eq_rank K

end IsCyclotomicExtension.Rat

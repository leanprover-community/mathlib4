/-
Copyright (c) 2022 Riccardo Brasca. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/

import Mathlib.NumberTheory.Cyclotomic.Discriminant
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
  refine (@Fintype.card_eq_zero_iff _ (_)).2 ⟨fun ⟨w, hwreal⟩ ↦ ?_⟩
  rw [isReal_iff] at hwreal
  let f := w.embedding
  let ζ := IsCyclotomicExtension.zeta (p ^ (k + 1)) ℚ K
  have hζ := (IsCyclotomicExtension.zeta_spec (p ^ (k + 1)) ℚ K)
  have hζ' : IsPrimitiveRoot (f ζ) (p ^ (k + 1)) := hζ.map_of_injective f.injective
  have him : (f ζ).im = 0 := by
    · rw [← conj_eq_iff_im, ← ComplexEmbedding.conjugate_coe_eq]
      congr
  have hre : (f ζ).re = 1 ∨ (f ζ).re = -1 := by
    · rw [← abs_re_eq_abs] at him
      have := Complex.norm_eq_one_of_pow_eq_one hζ'.pow_eq_one (by norm_num)
      rw [Complex.norm_eq_abs, ← him] at this
      by_cases hpos : 0 ≤ (f ζ).re
      · rw [_root_.abs_of_nonneg hpos] at this
        left
        exact this
      · rw [_root_.abs_of_neg (not_le.1 hpos)] at this
        right
        simp [← this]
  cases hre with
  | inl hone =>
    exact hζ'.ne_one (one_lt_pow hp.1.one_lt (succ_ne_zero k)) <| ext (by simp [hone])
      (by simp [him])
  | inr hnegone =>
    replace hζ' := hζ'.pow_eq_one
    rw [← re_add_im (f ζ), him, hnegone] at hζ'
    simp [(Prime.odd_of_ne_two hp.1 (fun H ↦ hodd <| PNat.eq H)).pow.neg_one_pow] at hζ'

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

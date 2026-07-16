/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-!
# Connection between pentagonal numbers and partitions
-/

variable (R : Type*) [CommRing R]

namespace Nat.Partition
open PowerSeries PowerSeries.WithPiTopology Finset

/-- This is a private intermediate lemma. See the public version that removes `[T2Space R]`
`hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts`. -/
theorem hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts'
    [TopologicalSpace R] [T2Space R] :
    HasProd (fun i ↦ 1 - X ^ (i + 1))
    (PowerSeries.mk fun n ↦ (#(evenCountDistincts n) - #(oddCountDistincts n) : R)) := by
  nontriviality R using Subsingleton.eq_one
  convert! ← hasProd_genFun (fun i c ↦ if c = 1 then (-1 : R) else 0) using 1
  · ext1 i
    simp [sub_eq_add_neg]
  rw [genFun]
  ext n
  simp_rw [coeff_mk, Finset.card_eq_sum_ones, cast_sum, cast_one, evenCountDistincts,
    oddCountDistincts, Finset.sum_filter, ← Finset.sum_sub_distrib, distincts, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ ↦ ?_)
  by_cases hdup : k.parts.Nodup
  · rw [Finsupp.prod]
    rw [Finset.prod_ite_of_true (fun i hi ↦ by
      have : i ∈ k.parts := by simpa using hi
      simpa using Multiset.count_eq_one_of_mem hdup this)]
    rw [Finset.prod_const, Multiset.toFinsupp_support, Multiset.toFinset_card_of_nodup hdup]
    rcases even_or_odd k.parts.card with heven | hodd
    · simp [hdup, heven, not_odd_iff_even.mpr heven]
    · simp [hdup, hodd, not_even_iff_odd.mpr hodd]
  · obtain ⟨i, hi⟩ : ∃ i, 1 < k.parts.count i := by
      simpa [Multiset.nodup_iff_count_le_one] using hdup
    have hic : (fun i ↦ if k.parts.count i = 1 then (-1 : R) else 0) i = 0 := by
      simp [hi.ne.symm]
    have hmem : i ∈ k.parts.toFinset := by simpa using Multiset.one_le_count_iff_mem.mp hi.le
    simpa [hdup, Finsupp.prod] using Finset.prod_eq_zero hmem hic

/-- The difference between `#(evenCountDistincts n)` and `#(oddCountDistincts n)` equals the `n`-th
  coefficent of `pentagonalSeries R`, which is `(-1)^k` for the `k`-th pentagonal number, and `0`
  for non-pentagonal numbers. (See also `PowerSeries.coeff_pentagonalSeries_eq_zero` and
  `PowerSeries.coeff_pentagonalSeries_pentagonal`) -/
public theorem card_evenCountDistincts_sub_card_oddCountDistincts (n : ℕ) :
    (#(evenCountDistincts n) - #(oddCountDistincts n) : R) = (pentagonalSeries R).coeff n  := by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts' R).unique
     (hasProd_one_sub_X_pow R)
  have hcoeff := congr(PowerSeries.coeff n $h)
  rw [PowerSeries.coeff_mk] at hcoeff
  exact hcoeff

/-- The generating function for `#(evenCountDistincts n) - #(oddCountDistincts n)` is
$\prod_{n=1}^{\infty} (1 - x^n)$. -/
public theorem hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts
    [TopologicalSpace R] :
    HasProd (fun i ↦ 1 - X ^ (i + 1))
    (PowerSeries.mk fun n ↦ (#(evenCountDistincts n) - #(oddCountDistincts n) : R)) := by
  simp_rw [card_evenCountDistincts_sub_card_oddCountDistincts]
  convert hasProd_one_sub_X_pow R
  ext n
  simp

/-- `#(evenCountDistincts n)` and `#(oddCountDistincts n)` are equal iff `n` is not a pentagonal
number. -/
public theorem card_evenCountDistincts_eq_card_oddCountDistincts_iff (n : ℕ) :
    #(evenCountDistincts n) = #(oddCountDistincts n) ↔ n ∉ Set.range pentagonal := by
  rw [← coeff_pentagonalSeries_eq_zero_iff ℤ, ← card_evenCountDistincts_sub_card_oddCountDistincts,
    sub_eq_zero, cast_inj]

end Nat.Partition

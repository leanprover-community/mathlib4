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

/-- The generating function for `#(evenCountDistincts n) - #(oddCountDistincts n)` is
$\prod_{n=1}^{\infty} (1 - x^n)$. -/
theorem hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts
    [TopologicalSpace R] :
    HasProd (fun i ↦ 1 - X ^ (i + 1))
      (PowerSeries.mk fun n ↦ (#(evenCountDistincts n) - #(oddCountDistincts n) : R)) := by
  convert! hasProd_genFunDistincts (fun i ↦ (-1 : R)) using 1
  · simp [sub_eq_add_neg]
  ext n
  simp_rw [coeff_mk, coeff_genFunDistincts, Multiset.map_const', Multiset.prod_replicate,
    card_eq_sum_ones, cast_sum, cast_one, evenCountDistincts, oddCountDistincts, sum_filter,
    ← sum_sub_distrib]
  congr with p
  rcases even_or_odd p.parts.card with heven | hodd
  · simp [heven, not_odd_iff_even.mpr heven]
  · simp [hodd, not_even_iff_odd.mpr hodd]

/-- The difference between `#(evenCountDistincts n)` and `#(oddCountDistincts n)` equals the `n`-th
  coefficent of `pentagonalSeries R`, which is `(-1)^k` for the `k`-th pentagonal number, and `0`
  for non-pentagonal numbers. (See also `PowerSeries.coeff_pentagonalSeries_eq_zero` and
  `PowerSeries.coeff_pentagonalSeries_pentagonal`) -/
public theorem card_evenCountDistincts_sub_card_oddCountDistincts (n : ℕ) :
    (#(evenCountDistincts n) - #(oddCountDistincts n) : R) = (pentagonalSeries R).coeff n  := by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts R).unique
     (hasProd_one_sub_X_pow R)
  have hcoeff := congr(coeff n $h)
  rw [coeff_mk] at hcoeff
  exact hcoeff

/-- `#(evenCountDistincts n)` and `#(oddCountDistincts n)` are equal iff `n` is not a pentagonal
number. -/
public theorem card_evenCountDistincts_eq_card_oddCountDistincts_iff (n : ℕ) :
    #(evenCountDistincts n) = #(oddCountDistincts n) ↔ n ∉ Set.range pentagonal := by
  rw [← coeff_pentagonalSeries_eq_zero_iff ℤ, ← card_evenCountDistincts_sub_card_oddCountDistincts,
    sub_eq_zero, cast_inj]

end Nat.Partition

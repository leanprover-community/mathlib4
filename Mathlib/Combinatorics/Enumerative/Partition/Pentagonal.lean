/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.RingTheory.PowerSeries.Pentagonal
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Partition.GenFun

/-!
# Connection between pentagonal numbers and partitions

* `card_evenCountDistincts_sub_card_oddCountDistincts_pentagonal`: for pentagonal number $a_k$,
  the difference between `#(evenCountDistincts a_k)` and `#(oddCountDistincts a_k)` is $(-1)^k$.
* `card_evenCountDistincts_eq_card_oddCountDistincts`: for `n` that's not a pentagonal number,
  `#(evenCountDistincts n) = #(evenCountDistincts n)`.
-/

theorem two_pentagonal (k : ℤ) : 2 * (k * (3 * k - 1) / 2) = k * (3 * k - 1) := by
  refine Int.two_mul_ediv_two_of_even ?_
  obtain h | h := Int.even_or_odd k
  · exact Even.mul_right h (3 * k - 1)
  · refine Even.mul_left (Int.even_sub_one.mpr (Int.not_even_iff_odd.mpr (Odd.mul ?_ h))) _
    decide

theorem pentagonal_nonneg (k : ℤ) : 0 ≤ k * (3 * k - 1) / 2 := by
  suffices 0 ≤ 2 * (k * (3 * k - 1) / 2) by simpa
  rw [two_pentagonal]
  obtain h | h := lt_or_ge 0 k
  · exact mul_nonneg h.le (by linarith)
  · exact mul_nonneg_of_nonpos_of_nonpos h (by linarith)

theorem two_pentagonal_inj {x y : ℤ} (h : x * (3 * x - 1) = y * (3 * y - 1)) : x = y := by
  simp_rw [mul_sub_one] at h
  rw [sub_eq_sub_iff_sub_eq_sub, mul_left_comm x, mul_left_comm y, ← mul_sub] at h
  rw [mul_self_sub_mul_self, ← mul_assoc, ← sub_eq_zero, ← sub_one_mul, mul_eq_zero] at h
  obtain h | h := h
  · simp [← Int.eq_of_mul_eq_one <| eq_of_sub_eq_zero h] at h
  · exact eq_of_sub_eq_zero h

theorem pentagonal_injective : Function.Injective (fun (k : ℤ) ↦ k * (3 * k - 1) / 2) := by
  intro a b h
  have : a * (3 * a - 1) = b * (3 * b - 1) := by
    rw [← two_pentagonal a, ← two_pentagonal b]
    simp [h]
  exact two_pentagonal_inj this

theorem toNat_pentagonal_injective :
    Function.Injective (fun (k : ℤ) ↦ (k * (3 * k - 1) / 2).toNat) := by
  intro a b h
  apply pentagonal_injective
  zify at h
  simpa [pentagonal_nonneg] using h

theorem toNat_pentagonal_inj {x y : ℤ}
    (h : (x * (3 * x - 1) / 2).toNat = (y * (3 * y - 1) / 2).toNat) : x = y := by
  apply toNat_pentagonal_injective.eq_iff.mp h

variable (R) [CommRing R] [TopologicalSpace R] [T2Space R]

namespace Nat.Partition
open PowerSeries PowerSeries.WithPiTopology Finset

public theorem hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts :
    HasProd (fun i ↦ 1 - X ^ (i + 1))
    (PowerSeries.mk fun n ↦ (#(evenCountDistincts n) - #(oddCountDistincts n) : R)) := by
  nontriviality R using Subsingleton.eq_one
  convert hasProd_genFun (fun i c ↦ if c = 1 then (-1 : R) else 0) using 1
  · ext1 i
    simp [sub_eq_add_neg]
  rw [genFun]
  ext n
  simp_rw [coeff_mk, Finset.card_eq_sum_ones, Nat.cast_sum, cast_one, evenCountDistincts,
    oddCountDistincts, Finset.sum_filter, ← Finset.sum_sub_distrib, distincts, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun k _ ↦ Eq.symm ?_)
  by_cases hdup : k.parts.Nodup
  · rw [Finsupp.prod]
    rw [Finset.prod_ite_of_true (fun i hi ↦ by
      have : i ∈ k.parts := by simpa using hi
      simpa using Multiset.count_eq_one_of_mem hdup this)]
    rw [Finset.prod_const, Multiset.toFinsupp_support, Multiset.toFinset_card_of_nodup hdup]
    rcases even_or_odd k.parts.card with heven | hodd
    · simp [hdup, heven, Nat.not_odd_iff_even.mpr heven]
    · simp [hdup, hodd, Nat.not_even_iff_odd.mpr hodd]
  · obtain ⟨i, hi⟩ : ∃ i, 1 < k.parts.count i := by
      simpa [Multiset.nodup_iff_count_le_one] using hdup
    have hic : (fun i ↦ if k.parts.count i = 1 then (-1 : R) else 0) i = 0 := by
      simp [hi.ne.symm]
    have hmem : i ∈ k.parts.toFinset := by simpa using Multiset.one_le_count_iff_mem.mp hi.le
    simpa [hdup, Finsupp.prod] using Finset.prod_eq_zero hmem hic

public theorem powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts_eq_tprod :
    (PowerSeries.mk fun n ↦ (#(evenCountDistincts n) - #(oddCountDistincts n) : R)) =
    ∏' i, (1 - X ^ (i + 1)) :=
  (hasProd_powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts R).tprod_eq.symm

public theorem powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts_eq_tsum
    [IsTopologicalRing R] :
    (PowerSeries.mk fun n ↦ (#(evenCountDistincts n) - #(oddCountDistincts n) : R)) =
    ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat :=
  (powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts_eq_tprod R).trans
  (tprod_one_sub_X_pow R)

public theorem card_evenCountDistincts_sub_card_oddCountDistincts_pentagonal (k : ℤ) :
    #(evenCountDistincts (k * (3 * k - 1) / 2).toNat) -
    #(oddCountDistincts (k * (3 * k - 1) / 2).toNat) = (k.negOnePow : ℤ) := by
  obtain h := congr(coeff (k * (3 * k - 1) / 2).toNat
    $(powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts_eq_tsum ℤ))
  rw [coeff_mk, (summable_pow_pentagonal ℤ).map_tsum _ (WithPiTopology.continuous_coeff _ _)] at h
  apply h.trans
  simp_rw [← smul_eq_mul]
  norm_cast
  simp_rw [coeff_smul, coeff_X_pow]
  rw [tsum_eq_single k fun l hl ↦ by
    contrapose! hl
    exact (toNat_pentagonal_inj <| by simpa using hl).symm]
  simp

public theorem card_evenCountDistincts_eq_card_oddCountDistincts {n : ℕ}
    (h : ∀ k : ℤ, (k * (3 * k - 1) / 2).toNat ≠ n) :
    #(evenCountDistincts n) = #(oddCountDistincts n) := by
  obtain heq := congr(coeff n
    $(powerSeriesMk_card_evenCountDistincts_sub_card_oddCountDistincts_eq_tsum ℤ))
  rw [coeff_mk, (summable_pow_pentagonal ℤ).map_tsum _ (WithPiTopology.continuous_coeff _ _)] at heq
  zify
  refine eq_of_sub_eq_zero (heq.trans ?_)
  convert tsum_zero with m n
  rw [← smul_eq_mul]
  norm_cast
  rw [coeff_smul, coeff_X_pow]
  simpa using (h m).symm

end Nat.Partition

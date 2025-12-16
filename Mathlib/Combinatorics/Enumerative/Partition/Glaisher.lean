/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Combinatorics.Enumerative.Partition.GenFun
public import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Glaisher's theorem

This file proves Glaisher's theorem: the number of partitions of an integer $n$ into parts not
divisible by $d$ is equal to the number of partitions in which no part is repeated $d$ or more
times.

## Main declarations
* `Nat.Partition.card_restricted_eq_card_countRestricted`: Glaisher's theorem.
* `Nat.Partition.card_odds_eq_card_distincts`: Euler's partition theorem, a special case
  of Glaisher's theorem when `m = 2`. This is also Theorem 45 from the
  [100 Theorems List](https://www.cs.ru.nl/~freek/100/).

## Proof outline

The proof is based on the generating functions for `restricted` and `countRestricted` partitions,
which turn out to be equal:

$$\prod_{i=1,i\nmid m}^\infty\frac{1}{1-X^i}=\prod_{i=0}^\infty (1+X^{i+1}+\cdots+X^{(m-1)(i+1)})$$

## References
https://en.wikipedia.org/wiki/Glaisher%27s_theorem
-/

@[expose] public section

variable (R) [TopologicalSpace R] [T2Space R]

namespace Nat.Partition
open PowerSeries PowerSeries.WithPiTopology Finset

section Semiring
variable [CommSemiring R]

/-- The generating function of `Nat.Partition.restricted n p` is
$$
\prod_{i \in p} \sum_{j = 0}^{\infty} X^{ij}
$$ -/
theorem hasProd_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    HasProd (fun i ↦ if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1)
    (PowerSeries.mk fun n ↦ (#(restricted n p) : R)) := by
  convert hasProd_genFun (fun i c ↦ if p i then (1 : R) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      simp_rw [pow_mul, pow_add]
      apply Summable.mul_right
      exact summable_pow_of_constantCoeff_eq_zero (by simp)
    · simp
  · simp_rw [genFun, restricted, card_filter, Finsupp.prod, prod_boole]
    simp

theorem multipliable_powerSeriesMk_card_restricted [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    Multipliable (fun i ↦ if p (i + 1) then ∑' j : ℕ, (X ^ ((i + 1) * j) : R⟦X⟧) else 1) :=
  (hasProd_powerSeriesMk_card_restricted R p).multipliable

theorem powerSeriesMk_card_restricted_eq_tprod [IsTopologicalSemiring R]
    (p : ℕ → Prop) [DecidablePred p] :
    PowerSeries.mk (fun n ↦ (#(restricted n p) : R)) =
    ∏' i, if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1 :=
  (hasProd_powerSeriesMk_card_restricted R p).tprod_eq.symm

/-- The generating function of `Nat.Partition.countRestricted n m` is
$$
\prod_{i = 1}^{\infty} \sum_{j = 0}^{m - 1} X^{ij}
$$ -/
theorem hasProd_powerSeriesMk_card_countRestricted {m : ℕ} (hm : 0 < m) :
    HasProd (fun i ↦ ∑ j ∈ range m, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (#(countRestricted n m) : R)) := by
  nontriviality R using Subsingleton.eq_one
  convert hasProd_genFun (fun i c ↦ if c < m then (1 : R) else 0) using 1
  · ext1 i
    rw [sum_range_eq_add_Ico _ hm, sum_Ico_eq_sum_range]
    congrm $(by simp) + ?_
    trans ∑ k ∈ range (m - 1), (if k + 1 < m then (1 : R) else 0) • X ^ ((i + 1) * (k + 1))
    · refine sum_congr rfl fun b hn ↦ ?_
      rw [add_comm 1 b]
      have : b + 1 < m := by grind
      simp [this]
    · exact (tsum_eq_sum (fun b hb ↦ smul_eq_zero_of_left (by simpa using hb) _)).symm
  · simp_rw [genFun, countRestricted, card_filter, Finsupp.prod, prod_boole]
    simp

theorem multipliable_powerSeriesMk_card_countRestricted (m : ℕ) :
    Multipliable fun i ↦ ∑ j ∈ range m, (X ^ ((i + 1) * j) : R⟦X⟧) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using multipliable_of_exists_eq_zero ⟨0, rfl⟩
  · exact (hasProd_powerSeriesMk_card_countRestricted R hm).multipliable

theorem powerSeriesMk_card_countRestricted_eq_tprod {m : ℕ} (hm : 0 < m) :
    PowerSeries.mk (fun n ↦ (#(countRestricted n m) : R)) =
    ∏' i, ∑ j ∈ range m, X ^ ((i + 1) * j) :=
  (hasProd_powerSeriesMk_card_countRestricted R hm).tprod_eq.symm

end Semiring

section Ring
variable [CommRing R] [NoZeroDivisors R]

private theorem aux_mul_one_sub_X_pow [IsTopologicalRing R] {m : ℕ} (hm : 0 < m) :
    (∏' i, if ¬m ∣ i + 1 then ∑' j, (X : R⟦X⟧) ^ ((i + 1) * j) else 1) * ∏' i, (1 - X ^ (i + 1)) =
    ∏' i, (1 - X ^ ((i + 1) * m)) := by
  nontriviality R
  rw [← (multipliable_powerSeriesMk_card_restricted R (¬ m ∣ ·)).tprod_mul
    (multipliable_one_sub_X_pow _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b ↦ _ =>
    ext b
    rw [tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
  refine tprod_eq_tprod_of_ne_one_bij (fun i ↦ (i.val + 1) * m - 1) ?_ ?_ ?_
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith), mul_left_inj' (hm.ne.symm), add_left_inj] at h
    exact SetCoe.ext h
  · suffices ∀ (i : ℕ), m ∣ i + 1 → ∃ j ≠ 0, j * m - 1 = i by simpa
    intro i hi
    obtain ⟨j, hj⟩ := dvd_def.mp hi
    refine ⟨j, by grind, Nat.sub_eq_of_eq_add ?_⟩
    rw [hj, mul_comm m j]
  · intro i
    have : (i + 1) * m - 1 + 1 = (i + 1) * m := by grind
    simp [this, pow_mul]

omit [TopologicalSpace R] in
theorem powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted {m : ℕ} (hm : 0 < m) :
    (PowerSeries.mk fun n ↦ (#(restricted n (¬ m ∣ ·)) : R)) =
    PowerSeries.mk fun n ↦ (#(countRestricted n m) : R) := by
  nontriviality R
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  rw [powerSeriesMk_card_restricted_eq_tprod R (¬ m ∣ ·)]
  rw [powerSeriesMk_card_countRestricted_eq_tprod R hm]
  apply mul_right_cancel₀ (tprod_one_sub_X_pow_ne_zero R)
  rw [aux_mul_one_sub_X_pow R hm]
  rw [← (multipliable_powerSeriesMk_card_countRestricted R m).tprod_mul
    (multipliable_one_sub_X_pow _)]
  exact tprod_congr (fun i ↦ by simp_rw [pow_mul, geom_sum_mul_neg])

end Ring

theorem card_restricted_eq_card_countRestricted (n : ℕ) {m : ℕ} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) := by
  simpa using PowerSeries.ext_iff.mp
    (powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted ℤ hm) n

theorem card_odds_eq_card_distincts (n : ℕ) : #(odds n) = #(distincts n) := by
  simp_rw [← countRestricted_two, odds, even_iff_two_dvd]
  exact card_restricted_eq_card_countRestricted n (by norm_num)

end Nat.Partition

/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# Glaisher's theorem

This file proves Glaisher's theorem: the number of partitions of an integer $n$ into parts not
divisible by $d$ is equal to the number of partitions in which no part is repeated $d$ or more
times.

## Main declarations
* `Nat.Partition.card_restricted_eq_card_countRestricted`: Glaisher's theorem.

## References
https://en.wikipedia.org/wiki/Glaisher%27s_theorem
-/

variable (M) [TopologicalSpace M]

namespace PowerSeries.WithPiTopology

section Semiring
variable [Semiring M]

theorem summable_X_pow_add_one_mul_add (i : ℕ) (k : ℕ) :
    Summable fun j ↦ (X : M⟦X⟧) ^ ((i + 1) * (j + k)) := by
  rcases subsingleton_or_nontrivial M with h | h
  · simpa [Subsingleton.eq_zero] using summable_zero
  apply summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n + 1, ?_⟩)
  intro m hm
  rw [order_X_pow]
  norm_cast
  nlinarith

end Semiring

section CommRing
variable [CommRing M]

theorem multipliable_one_sub_X_pow : Multipliable fun n ↦ (1 : M⟦X⟧) - X ^ (n + 1) := by
  rcases subsingleton_or_nontrivial M with h | h
  · simpa [Subsingleton.eq_one] using multipliable_one
  simp_rw [sub_eq_add_neg]
  apply multipliable_one_add_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr (fun n ↦ Filter.eventually_atTop.mpr ⟨n, ?_⟩)
  intro m hm
  rw [order_neg, order_X_pow]
  norm_cast
  nlinarith

theorem tprod_one_sub_X_pow_ne_zero [T2Space M] [Nontrivial M] :
    ∏' i, (1 - X ^ (i + 1)) ≠ (0 : M⟦X⟧) := by
  by_contra! h
  obtain h := PowerSeries.ext_iff.mp h 0
  simp [coeff_zero_eq_constantCoeff, Multipliable.map_tprod (multipliable_one_sub_X_pow M) _
    (WithPiTopology.continuous_constantCoeff M)] at h

end CommRing

end PowerSeries.WithPiTopology

namespace Nat.Partition
open PowerSeries Finset
open scoped PowerSeries.WithPiTopology

section Semiring
variable [CommSemiring M]

/-- The generating function of `Nat.Partition.restricted n p` is
$$
\prod_{i \mem p} \sum_{j = 0}^{\infty} X^{ij}
$$ -/
theorem hasProd_powerSeriesMk_card_restricted [T2Space M] [IsTopologicalSemiring M]
    (p : ℕ → Prop) [DecidablePred p] :
    HasProd (fun i ↦ if p (i + 1) then ∑' j : ℕ, X ^ ((i + 1) * j) else 1)
    (PowerSeries.mk fun n ↦ (#(restricted n p) : M)) := by
  convert hasProd_genFun (fun i c ↦ if p i then (1 : M) else 0) using 1
  · ext1 i
    split_ifs
    · rw [tsum_eq_zero_add' ?_]
      · simp
      exact (WithPiTopology.summable_X_pow_add_one_mul_add M i 1)
    · simp
  · simp_rw [genFun, restricted, Finset.card_filter, Finset.prod_boole]
    simp

/-- The generating function of `Nat.Partition.countRestricted n m` is
$$
\prod_{i = 1}^{\infty} \sum_{j = 0}^{m - 1} X^{ij}
$$ -/
theorem hasProd_powerSeriesMk_card_countRestricted [T2Space M] {m : ℕ} (hm : 0 < m) :
    HasProd (fun i ↦ ∑ j ∈ Finset.range m, X ^ ((i + 1) * j))
    (PowerSeries.mk fun n ↦ (#(countRestricted n m) : M)) := by
  rcases subsingleton_or_nontrivial M with h | h
  · simp [Subsingleton.eq_one, HasProd]
  convert hasProd_genFun (fun i c ↦ if c < m then (1 : M) else 0) using 1
  · ext1 i
    rw [Finset.sum_range_eq_add_Ico _ hm, Finset.sum_Ico_eq_sum_range]
    congrm $(by simp) + ?_
    trans ∑ k ∈ range (m - 1), (if k + 1 < m then (1 : M) else 0) • X ^ ((i + 1) * (k + 1))
    · refine Finset.sum_congr rfl fun b hn ↦ ?_
      rw [add_comm 1 b]
      have : b + 1 < m := by grind
      simp [this]
    · exact (tsum_eq_sum (fun b hb ↦ smul_eq_zero_of_left (by simpa using hb) _)).symm
  · simp_rw [genFun, countRestricted, Finset.card_filter, Finset.prod_boole]
    simp

end Semiring

section Ring
variable [CommRing M] [NoZeroDivisors M]

private theorem aux_mul_one_sub_X_pow [T2Space M] [IsTopologicalRing M] {m : ℕ} (hm : 0 < m) :
    (∏' i, if ¬m ∣ i + 1 then ∑' j, (X : M⟦X⟧) ^ ((i + 1) * j) else 1) *
    ∏' i, (1 - X ^ (i + 1)) = ∏' i, (1 - X ^ ((i + 1) * m)) := by
  rcases subsingleton_or_nontrivial M with h | h
  · simp [Subsingleton.eq_one]
  rw [← Multipliable.tprod_mul (hasProd_powerSeriesMk_card_restricted M (¬ m ∣ ·)).multipliable
    (WithPiTopology.multipliable_one_sub_X_pow _)]
  simp_rw [ite_not, ite_mul, pow_mul]
  conv in fun b ↦ _ =>
    ext b
    rw [WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero (by simp)]
  refine tprod_eq_tprod_of_ne_one_bij (fun i ↦ (i.val + 1) * m - 1) ?_ ?_ ?_
  · intro a b h
    rw [tsub_left_inj (by nlinarith) (by nlinarith), mul_left_inj' (hm.ne.symm), add_left_inj] at h
    exact SetCoe.ext h
  · suffices ∀ (i : ℕ), m ∣ i + 1 → ∃ a, (a + 1) * m - 1 = i by simpa
    intro i hi
    obtain ⟨j, hj⟩ := dvd_def.mp hi
    refine ⟨j - 1, Nat.sub_eq_of_eq_add ?_⟩
    rw [hj, mul_comm m j, Nat.sub_add_cancel (by grind)]
  · intro i
    have : (i + 1) * m - 1 + 1 = (i + 1) * m := Nat.sub_add_cancel (by nlinarith)
    simp [this, pow_mul]

omit [TopologicalSpace M] in
theorem powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted
    {m : ℕ} (hm : 0 < m) :
    (PowerSeries.mk fun n ↦ (#(restricted n (¬ m ∣ ·)) : M)) =
    PowerSeries.mk fun n ↦ (#(countRestricted n m) : M) := by
  let _ : TopologicalSpace M := ⊥
  have _ : DiscreteTopology M := ⟨rfl⟩
  refine ((hasProd_powerSeriesMk_card_restricted M (¬ m ∣ ·)).tprod_eq.symm.trans ?_).trans
    (hasProd_powerSeriesMk_card_countRestricted M hm).tprod_eq
  rcases subsingleton_or_nontrivial M with h | h
  · simp [Subsingleton.eq_one]
  apply mul_right_cancel₀ (WithPiTopology.tprod_one_sub_X_pow_ne_zero M)
  apply (aux_mul_one_sub_X_pow M hm).trans
  rw [← Multipliable.tprod_mul (hasProd_powerSeriesMk_card_countRestricted M hm).multipliable
    (WithPiTopology.multipliable_one_sub_X_pow _)]
  exact tprod_congr (fun i ↦ by simp_rw [pow_mul, geom_sum_mul_neg])

end Ring

theorem card_restricted_eq_card_countRestricted (n : ℕ) {m : ℕ} (hm : 0 < m) :
    #(restricted n (¬ m ∣ ·)) = #(countRestricted n m) := by
  simpa using PowerSeries.ext_iff.mp
    (powerSeriesMk_card_restricted_eq_powerSeriesMk_card_countRestricted ℤ hm) n

end Nat.Partition

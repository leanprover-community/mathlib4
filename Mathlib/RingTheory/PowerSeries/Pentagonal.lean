/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.RingTheory.PowerSeries.PiTopology

import Mathlib.Topology.Algebra.InfiniteSum.Pentagonal

/-!
# Pentagonal number theorem for power series

This file proves the pentagonal number theorem for power series:

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{a_k} $$

where $a_k = k(3k - 1)/2$ are the pentagonal numbers.

See also `PowerSeries.WithPiTopology.multipliable_one_sub_X_pow` for multipliability of the
left-hand side.

## Main theorems

* `PowerSeries.WithPiTopology.tprod_one_sub_X_pow`: pentagonal number theorem following the equation
  above.
  * `PowerSeries.WithPiTopology.summable_pow_pentagonal`: summability of the right-hand side.
* `PowerSeries.WithPiTopology.tprod_one_sub_X_pow'`: pentagonal number
  theorem in the opposite summing order $\sum_{k=-\infty}^{\infty} (-1)^k x^{a_{-k}}$.
  * `PowerSeries.WithPiTopology.summable_pow_pentagonal'`: summability of the right-hand side.
* `PowerSeries.WithPiTopology.tprod_one_sub_X_pow_eq_tsum_nat` pentagonal number
  theorem for summing over natural numbers by grouping terms in pairs
  `$\sum_{k=0}^{\infty} (-1)^k (x^{a_{-k}} - x^{a_{k+1}})$.
  * `PowerSeries.WithPiTopology.summable_pow_pentagonal_sub`: summability of the right-hand side.
-/

open Filter PowerSeries WithPiTopology
variable (R : Type*) [CommRing R]

namespace Pentagonal

theorem tendsTo_order_aux_X (k : ℕ) :
    Tendsto (fun i ↦ (aux k i (X : R⟦X⟧)).order) atTop (nhds ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [aux, ← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind

theorem tendsTo_order_neg_X_pow (k : ℕ) :
    Tendsto (fun i ↦ (-(X : R⟦X⟧) ^ (i + k + 1)).order) atTop (nhds ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩
  intro m hm
  rw [order_neg, order_X_pow]
  norm_cast
  linarith

theorem tendsTo_order_pow_pentagonal_sub :
    Tendsto (fun i ↦ ((-1) ^ i * ((X : R⟦X⟧) ^ (i * (3 * i + 1) / 2) -
      X ^ ((i + 1) * (3 * i + 2) / 2))).order) atTop (nhds ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro k hk
  rw [sub_eq_add_neg]
  grw [← le_order_mul, ← min_order_le_order_add, order_neg, order_X_pow, order_X_pow]
  apply lt_add_of_nonneg_of_lt (by simp) ?_
  rw [min_eq_left (by gcongr <;> simp)]
  rw [Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  exact Nat.mul_le_mul hk (by linarith)

end Pentagonal

variable [TopologicalSpace R]

namespace Pentagonal

theorem summable_aux_X (k : ℕ) : Summable (aux k · (X : R⟦X⟧)) :=
  summable_of_tendsto_order_atTop_nhds_top R (tendsTo_order_aux_X R k)

theorem multipliable_one_sub_X_pow (k : ℕ) : Multipliable fun n ↦ (1 : R⟦X⟧) - X ^ (n + k + 1) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsTo_order_neg_X_pow R k)

end Pentagonal

public section Public
namespace PowerSeries.WithPiTopology

theorem summable_pow_pentagonal_sub : Summable fun (k : ℕ) ↦
    ((-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) : R⟦X⟧) :=
  summable_of_tendsto_order_atTop_nhds_top R (Pentagonal.tendsTo_order_pow_pentagonal_sub R)

/-- **Pentagonal number theorem** for power series, summing over natural numbers:

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} - x^{(k+1)(3k+2)/2}\right) $$ -/
theorem tprod_one_sub_X_pow_eq_tsum_nat [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) =
    ∑' k, (-1) ^ k * (X ^ (k * (3 * k + 1) / 2) - X ^ ((k + 1) * (3 * k + 2) / 2)) := by
  nontriviality R
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun i (hi : i ≥ d + 1) ↦ ?_
    grind [coeff_X_pow]
  · apply Pentagonal.summable_aux_X
  · apply Pentagonal.multipliable_one_sub_X_pow
  · apply summable_pow_pentagonal_sub
  · rw [tendsto_iff_coeff_tendsto]
    refine fun n ↦ tendsto_atTop_of_eventually_const fun k (hk : k ≥ n) ↦ ?_
    rw [map_zero]
    apply coeff_of_lt_order
    grw [← le_order_mul, ← le_order_mul]
    refine (lt_add_of_lt_of_nonneg (lt_add_of_nonneg_of_lt (by simp) ?_) (by simp))
    rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
    apply Nat.mul_le_mul <;> linarith

theorem summable_pow_pentagonal' [IsTopologicalRing R] :
    Summable fun k ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat := by
  nontriviality R
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  apply summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩
  intro k hk
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  norm_cast
  grind

/-- **Pentagonal number theorem** for power series, summing over integers written using the
exponent $a_{-k}$ where $a_k = k(3k - 1)/2$ are the generalized pentagonal numbers.
Note that $a_{-k} = (-k)(3(-k) - 1)/2 = k(3k + 1)/2$, which explains the exponent in the
following formula:

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k + 1)/2} $$ -/
theorem tprod_one_sub_X_pow' [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k + 1) / 2).toNat := by
  rw [← tsum_nat_add_neg_add_one (summable_pow_pentagonal' R), tprod_one_sub_X_pow_eq_tsum_nat]
  refine tsum_congr fun k ↦ ?_
  rw [sub_eq_add_neg _ (X ^ _), mul_add, ← neg_mul_comm]
  congrm ($(by norm_cast) * X ^ $(by norm_cast) + ?_ * X ^ $(by norm_cast))
  trans (-1) ^ (k + 1)
  · ring
  · norm_cast

theorem summable_pow_pentagonal [IsTopologicalRing R] :
    Summable fun k ↦ (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat := by
  rw [← neg_injective.summable_iff (fun x hx ↦ by absurd hx; use -x; simp)]
  convert summable_pow_pentagonal' R
  rw [Function.comp_apply]
  exact congr($(by simp) * X ^ (Int.toNat ($(by ring_nf) / 2)))

/-- **Pentagonal number theorem** for power series, summing over integers written using the
exponent $a_k$ where $a_k = k(3k - 1)/2$ are the generalized pentagonal numbers:

$$ \prod_{n = 0}^{\infty} 1 - x^{n + 1} = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k - 1)/2} $$ -/
theorem tprod_one_sub_X_pow [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ (k * (3 * k - 1) / 2).toNat := by
  rw [tprod_one_sub_X_pow', ← neg_injective.tsum_eq (by simp)]
  exact tsum_congr fun k ↦ congr($(by simp) * X ^ (Int.toNat ($(by ring_nf) / 2)))

end PowerSeries.WithPiTopology
end Public

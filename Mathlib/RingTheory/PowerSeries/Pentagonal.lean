/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Pentagonal
public import Mathlib.RingTheory.PowerSeries.PiTopology

import Mathlib.Topology.Algebra.InfiniteSum.Pentagonal

/-!
# Pentagonal number theorem for power series

This file proves the pentagonal number theorem for power series:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{a_k} $$

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
* `PowerSeries.coeff_prod_one_sub_X_eventually_eq_negOnePow` and
  `PowerSeries.coeff_prod_one_sub_X_eventually_eq_zero`: coefficients of finite product
  $\prod_{n\in s} (1 - x^{n + 1})$ are eventually constants, either $(-1)^k$ or 0 depending whether
  the exponent on $x$ is a pentagonal number or not, respectively. These theorems don't assume any
  topology on the ring.
-/

open Filter PowerSeries WithPiTopology
variable (R : Type*) [CommRing R]

namespace Pentagonal

theorem tendsto_order_powMulProdOneSubPow_X (k : ℕ) :
    Tendsto (fun i ↦ (powMulProdOneSubPow k i (X : R⟦X⟧)).order) atTop (nhds ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [powMulProdOneSubPow, ← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind

theorem tendsto_order_neg_X_pow (k : ℕ) :
    Tendsto (fun i ↦ (-(X : R⟦X⟧) ^ (i + k + 1)).order) atTop (nhds ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩
  intro m hm
  rw [order_neg, order_X_pow]
  norm_cast
  linarith

theorem tendsto_order_pow_pentagonal_sub :
    Tendsto (fun (i : ℕ) ↦ ((-1) ^ i * ((X : R⟦X⟧) ^ pentagonal (-i) -
      X ^ (pentagonal (i + 1)))).order) atTop (nhds ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro k hk
  rw [sub_eq_add_neg]
  grw [← le_order_mul, ← min_order_le_order_add, order_neg, order_X_pow, order_X_pow]
  apply lt_add_of_nonneg_of_lt (by simp) ?_
  rw [min_eq_left (by simpa using (pentagonal_neg_lt_pentagonal_add_one (Int.natCast_nonneg k)).le)]
  rw [pentagonal_neg]
  norm_cast
  rw [Int.toNat_natCast, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
  exact Nat.mul_le_mul hk (by linarith)

end Pentagonal


namespace Pentagonal
variable [TopologicalSpace R]

theorem summable_powMulProdOneSubPow_X (k : ℕ) : Summable (powMulProdOneSubPow k · (X : R⟦X⟧)) :=
  summable_of_tendsto_order_atTop_nhds_top R (tendsto_order_powMulProdOneSubPow_X R k)

theorem multipliable_one_sub_X_pow (k : ℕ) : Multipliable fun n ↦ (1 : R⟦X⟧) - X ^ (n + k + 1) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsto_order_neg_X_pow R k)

end Pentagonal

public section Public
namespace PowerSeries
namespace WithPiTopology
variable [TopologicalSpace R]

theorem summable_pow_pentagonal_sub : Summable fun (k : ℕ) ↦
    ((-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)) : R⟦X⟧) :=
  summable_of_tendsto_order_atTop_nhds_top R (Pentagonal.tendsto_order_pow_pentagonal_sub R)

set_option backward.isDefEq.respectTransparency false in
/-- **Pentagonal number theorem** for power series, summing over natural numbers:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) =
\sum_{k=0}^{\infty} (-1)^k \left(x^{k(3k+1)/2} - x^{(k+1)(3k+2)/2}\right) $$ -/
theorem tprod_one_sub_X_pow_eq_tsum_nat [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) =
    ∑' (k : ℕ), (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)) := by
  nontriviality R
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun i (hi : i ≥ d + 1) ↦ ?_
    grind [coeff_X_pow]
  · apply Pentagonal.summable_powMulProdOneSubPow_X
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
    Summable fun k ↦ (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal (-k) := by
  nontriviality R
  apply Summable.of_add_one_of_neg_add_one
  all_goals
  apply summable_of_tendsto_order_atTop_nhds_top
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n, ?_⟩
  intro k hk
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_nonneg_of_lt (by simp) ?_
  rw [pentagonal_def]
  norm_cast
  grind

/-- **Pentagonal number theorem** for power series, summing over integers written using the
exponent $a_{-k}$ where $a_k = k(3k - 1)/2$ are the generalized pentagonal numbers.
Note that $a_{-k} = (-k)(3(-k) - 1)/2 = k(3k + 1)/2$, which explains the exponent in the
following formula:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k + 1)/2} $$ -/
theorem tprod_one_sub_X_pow' [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal (-k) := by
  rw [← tsum_nat_add_neg_add_one (summable_pow_pentagonal' R), tprod_one_sub_X_pow_eq_tsum_nat]
  refine tsum_congr fun k ↦ ?_
  rw [sub_eq_add_neg _ (X ^ _), mul_add, ← neg_mul_comm]
  congrm ($(by norm_cast) * X ^ $(by norm_cast) + ?_ * X ^ $(by norm_cast))
  trans (-1) ^ (k + 1)
  · ring
  · norm_cast

theorem summable_pow_pentagonal [IsTopologicalRing R] :
    Summable fun k ↦ (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k := by
  rw [← neg_injective.summable_iff (fun x hx ↦ by absurd hx; use -x; simp)]
  convert summable_pow_pentagonal' R
  rw [Function.comp_apply]
  congrm $(by simp) * X ^ _

/-- **Pentagonal number theorem** for power series, summing over integers written using the
exponent $a_k$ where $a_k = k(3k - 1)/2$ are the generalized pentagonal numbers:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{k(3k - 1)/2} $$ -/
theorem tprod_one_sub_X_pow [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1)) = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k := by
  rw [tprod_one_sub_X_pow', ← neg_injective.tsum_eq (by simp)]
  congrm ∑' k, $(by simp) * X ^ pentagonal $(by simp)

end WithPiTopology

open WithPiTopology

theorem coeff_prod_one_sub_X_eventually_eq_negOnePow (k : ℤ) :
    ∀ᶠ s in atTop, (∏ n ∈ s, (1 - X ^ (n + 1) : R⟦X⟧)).coeff (pentagonal k) = Int.negOnePow k := by
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  obtain h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow R, HasProd, tendsto_iff_coeff_tendsto] at h
  specialize h (pentagonal k)
  rw [(summable_pow_pentagonal R).map_tsum _ (WithPiTopology.continuous_coeff _ _),
    SummationFilter.unconditional_filter, nhds_discrete, tendsto_pure] at h
  have hpow (i : ℤ) : (i.negOnePow : R⟦X⟧) = C (i.negOnePow : R) := by simp
  simp_rw [hpow, coeff_C_mul, coeff_X_pow] at h
  rw [tsum_eq_single k fun i hi ↦ by simp [hi.symm]] at h
  simpa using h

theorem coeff_prod_one_sub_X_eventually_eq_zero {n : ℕ} (hn : ∀ k : ℤ, n ≠ pentagonal k) :
    ∀ᶠ s in atTop, (∏ n ∈ s, (1 - X ^ (n + 1) : R⟦X⟧)).coeff n = 0 := by
  let _ : TopologicalSpace R := ⊥
  have _ : DiscreteTopology R := ⟨rfl⟩
  obtain h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow R, HasProd, tendsto_iff_coeff_tendsto] at h
  specialize h n
  rw [(summable_pow_pentagonal R).map_tsum _ (WithPiTopology.continuous_coeff _ _),
    SummationFilter.unconditional_filter, nhds_discrete, tendsto_pure] at h
  have hpow (i : ℤ) : (i.negOnePow : R⟦X⟧) = C (i.negOnePow : R) := by simp
  simp_rw [hpow, coeff_C_mul, coeff_X_pow] at h
  simpa [hn] using h

end PowerSeries
end Public

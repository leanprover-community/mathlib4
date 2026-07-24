/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.Combinatorics.Enumerative.Pentagonal.Basic
public import Mathlib.RingTheory.PowerSeries.PiTopology

import Mathlib.Combinatorics.Enumerative.Pentagonal.Ring
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Pentagonal number theorem for power series

This file proves the pentagonal number theorem for power series:

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{a_k} $$

where $a_k = k(3k - 1)/2$ are the pentagonal numbers. We state the theorem in two parts by
introducing the intermediate power series `PowerSeries.pentagonalSeries`, whose coefficients are
defined using pentagonal numbers. We then show that this series is equal to both sides.

## Main theorems

* `PowerSeries.WithPiTopology.hasProd_one_sub_X_pow`: `PowerSeries.pentagonalSeries` is equal to
  infinite product on the left-hand side of the formula.
* `PowerSeries.coeff_prod_one_sub_X_pow_eventually_eq` restates the left-hand side without requiring
  topology.
* `PowerSeries.WithPiTopology.hasSum_pentagonalSeries`: `PowerSeries.pentagonalSeries` is equal to
  the infinite sum on the right-hand side of the formula.
* `PowerSeries.coeff_pentagonalSeries` restates the right-hand side without requiring topology.
-/

open Filter PowerSeries WithPiTopology Topology
variable (R : Type*) [CommRing R]

namespace Pentagonal
-- private auxiliary lemma

theorem tendsto_order_pow_mul_prod_one_sub_pow (k : ℕ) :
    Tendsto (fun n ↦ (X ^ ((k + 1) * n) *
      ∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧).order) atTop (𝓝 ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  refine ENat.tendsto_nhds_top_iff_natCast_lt.mpr fun n ↦ eventually_atTop.mpr ⟨n + 1, ?_⟩
  intro m hm
  grw [← le_order_mul, order_X_pow]
  refine lt_add_of_lt_of_nonneg ?_ (by simp)
  norm_cast
  grind

theorem tendsto_order_neg_X_pow (k : ℕ) :
    Tendsto (fun i ↦ (-(X : R⟦X⟧) ^ (i + k + 1)).order) atTop (𝓝 ⊤) := by
  nontriviality R using Subsingleton.eq_zero
  simp_rw [order_neg, order_X_pow, add_assoc]
  exact ENat.tendsto_natCast_nhds_top.comp (tendsto_add_atTop_nat _)

variable [TopologicalSpace R]

theorem summable_pow_mul_prod_one_sub_pow (k : ℕ) :
    Summable
      fun n ↦ (X ^ ((k + 1) * n) * ∏ i ∈ Finset.range (n + 1), (1 - X ^ (k + i + 1)) : R⟦X⟧) :=
  summable_of_tendsto_order_atTop_nhds_top R (tendsto_order_pow_mul_prod_one_sub_pow R k)

theorem multipliable_one_sub_X_pow (k : ℕ) : Multipliable fun n ↦ (1 : R⟦X⟧) - X ^ (n + k + 1) := by
  simpa [sub_eq_add_neg] using
    multipliable_one_add_of_tendsto_order_atTop_nhds_top R (tendsto_order_neg_X_pow R k)

end Pentagonal

public section Public
namespace PowerSeries

open Classical in
/-- The power series $\sum_{k=-\infty}^{\infty}(-1)^k x^{k * (3k - 1) / 2}$. -/
noncomputable
def pentagonalSeries : R⟦X⟧ :=
  .mk fun n ↦ if h : ∃ k, pentagonal k = n then
    Int.negOnePow h.choose
  else
    0

theorem coeff_pentagonalSeries_eq_zero {n : ℕ} (h : n ∉ Set.range pentagonal) :
    (pentagonalSeries R).coeff n = 0 := dif_neg <| by simpa using h

@[simp]
theorem coeff_pentagonalSeries_pentagonal (k : ℤ) :
    (pentagonalSeries R).coeff (pentagonal k) = Int.negOnePow k := by
  simp [pentagonalSeries]

@[simp]
theorem coeff_pentagonalSeries_eq_zero_iff [Nontrivial R] {n : ℕ} :
    (pentagonalSeries R).coeff n = 0 ↔ n ∉ Set.range pentagonal := by
  grind [pentagonalSeries, coeff_mk, neg_one_pow_ne_zero, Int.coe_negOnePow]

namespace WithPiTopology
variable [TopologicalSpace R]

/-- `PowerSeries.pentagonalSeries` as an infinite sum over integers -/
theorem hasSum_pentagonalSeries :
    HasSum (fun k : ℤ ↦ (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k) (pentagonalSeries R) := by
  suffices HasSum ((fun n ↦ C ((pentagonalSeries R).coeff n) * X ^ n) ∘ pentagonal)
      (pentagonalSeries R) by
    convert this
    simp
  rw [pentagonal_injective.hasSum_iff fun n hn ↦ by simp [coeff_pentagonalSeries_eq_zero R hn]]
  simpa [monomial_eq_C_mul_X_pow] using (pentagonalSeries R).hasSum_of_monomials_self

theorem pentagonalSeries_eq_tsum [T2Space R] :
    pentagonalSeries R = ∑' k, (Int.negOnePow k : R⟦X⟧) * X ^ pentagonal k :=
  (hasSum_pentagonalSeries R).tsum_eq.symm

/-- `PowerSeries.pentagonalSeries` as an infinite sum over natural numbers. In this version, terms
are ordered by strictly increasing exponent `pentagonal k` for `k = 0, 1, -1, 2, -2, 3, ...`,
and every two terms are grouped together. -/
theorem hasSum_pow_pentagonal_sub_pentagonalSeries :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)))
      (pentagonalSeries R) := by
  have h := hasSum_pentagonalSeries R
  rw [← neg_injective.hasSum_iff (fun x hx ↦ by absurd hx; use -x; simp)] at h
  convert h.nat_add_neg_add_one using 2 with k
  simp_rw [Function.comp_apply, neg_neg, Int.negOnePow_add]
  simp
  ring

theorem pentagonalSeries_eq_tsum_pow_pentagonal_sub [T2Space R] :
    pentagonalSeries R = ∑' (k : ℕ), (-1) ^ k * (X ^ pentagonal (-k) - X ^ pentagonal (k + 1)) :=
  (hasSum_pow_pentagonal_sub_pentagonalSeries R).tsum_eq.symm

/-- See the public version `PowerSeries.WithPiTopology.tprod_one_sub_X_pow` that removes
`IsTopologicalRing`. -/
private theorem tprod_one_sub_X_pow' [IsTopologicalRing R] [T2Space R] :
    ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R := by
  nontriviality R
  rw [pentagonalSeries_eq_tsum_pow_pentagonal_sub]
  refine Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_
  · rw [IsTopologicallyNilpotent, tendsto_iff_coeff_tendsto]
    refine fun d ↦ tendsto_atTop_of_eventually_const fun i (hi : i ≥ d + 1) ↦ ?_
    grind
  · exact Pentagonal.summable_pow_mul_prod_one_sub_pow R
  · exact Pentagonal.multipliable_one_sub_X_pow R
  · exact (hasSum_pow_pentagonal_sub_pentagonalSeries R).summable
  · rw [tendsto_iff_coeff_tendsto]
    refine fun n ↦ tendsto_atTop_of_eventually_const fun k (hk : k ≥ n) ↦ ?_
    rw [map_zero]
    apply coeff_of_lt_order
    grw [← le_order_mul, ← le_order_mul]
    refine (lt_add_of_lt_of_nonneg (lt_add_of_nonneg_of_lt (by simp) ?_) (by simp))
    rw [order_X_pow, Nat.cast_lt, ← Nat.add_one_le_iff, Nat.le_div_iff_mul_le (by simp)]
    apply Nat.mul_le_mul <;> linarith

end WithPiTopology

/-- **Pentagonal number theorem** for power series, expressed as the statement that the coefficients
of the product `∏ n, 1 - X ^ (n + 1)` are eventually constants as `(pentagonalSeries R).coeff`. -/
theorem coeff_prod_one_sub_X_pow_eventually_eq (n : ℕ) :
    ∀ᶠ s in atTop, (∏ n ∈ s, (1 - X ^ (n + 1) : R⟦X⟧)).coeff n = (pentagonalSeries R).coeff n := by
  let : TopologicalSpace R := ⊥
  have : DiscreteTopology R := ⟨rfl⟩
  have h := (multipliable_one_sub_X_pow R).hasProd
  rw [tprod_one_sub_X_pow' R, HasProd, tendsto_iff_coeff_tendsto] at h
  simpa using h n

namespace WithPiTopology
variable [TopologicalSpace R]

/-- **Pentagonal number theorem** for power series, expressed as an infinite product. See also
`PowerSeries.WithPiTopology.hasSum_pentagonalSeries` that expresses `pentagonalSeries` as an
infinite sum. -/
theorem hasProd_one_sub_X_pow :
    HasProd (fun n ↦ (1 - X ^ (n + 1) : R⟦X⟧)) (pentagonalSeries R) := by
  rw [HasProd, tendsto_iff_coeff_tendsto]
  intro n
  apply tendsto_nhds_of_eventually_eq
  simpa using coeff_prod_one_sub_X_pow_eventually_eq R n

theorem tprod_one_sub_X_pow [T2Space R] : ∏' n, (1 - X ^ (n + 1) : R⟦X⟧) = pentagonalSeries R :=
  (hasProd_one_sub_X_pow R).tprod_eq

end WithPiTopology
end PowerSeries
end Public

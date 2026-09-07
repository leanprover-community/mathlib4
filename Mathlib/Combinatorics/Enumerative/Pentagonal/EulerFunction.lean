/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Combinatorics.Enumerative.Pentagonal.PowerSeries

import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Combinatorics.Enumerative.Pentagonal.Ring

/-!
# Euler function and pentagonal number theorem

This file proves the pentagonal number theorem for $‖x‖ < 1$ in a complete normed ring (e.g. `ℂ`):

$$ \prod_{n = 0}^{\infty} (1 - x^{n + 1}) = \sum_{k=-\infty}^{\infty} (-1)^k x^{a_k} $$

where $a_k = k(3k - 1)/2$ are the pentagonal numbers. We state the theorem in two parts by
introducing the Euler function `eulerFunction`, defined as a power series whose coefficients are
related to pentagonal numbers. We then show that this function is equal to both sides.

## Main theorems

* `eulerFunction_eq_tprod`: `eulerFunction` is equal to the infinite product on the left-hand side.
* `eulerFunction_eq_tsum_pentagonal`: `eulerFunction` is equal to the infinite sum on the
  right-hand side.

## References

* https://en.wikipedia.org/wiki/Euler_function
-/

open Filter Finset

variable {R : Type*} [NormedCommRing R] [NormOneClass R]

namespace Pentagonal
-- Private section to supply lemma for using `Pentagonal.tprod_one_sub_pow`

lemma pow_mul_prod_bound (k n : ℕ) {x : R} (hx : ‖x‖ < 1) :
    ‖x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤
      ‖x‖ ^ ((k + 1) * n) * ∏' i, (1 + ‖x‖ ^ i) := by
  grw [norm_mul_le, Finset.norm_prod_le, norm_pow_le]
  refine mul_le_mul_of_nonneg_left ?_ (by simp)
  trans ∏ i ∈ Ico (k + 1) (n + 1 + (k + 1)), (1 + ‖x‖ ^ i)
  · rw [prod_Ico_eq_prod_range, Nat.add_sub_cancel]
    gcongr
    grw [norm_sub_le, norm_one, norm_pow_le, add_right_comm]
  have : Multipliable (1 + ‖x‖ ^ ·) := multipliable_one_add_of_summable (by simpa using hx)
  exact this.prod_le_tprod_of_nonneg (fun i _ ↦ by positivity) (by simp)

lemma summable_norm_pow_mul_prod (k : ℕ) {x : R} (hx : ‖x‖ < 1) :
    Summable fun n ↦ ‖x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ := by
  refine (Summable.mul_right _ ?_).of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (pow_mul_prod_bound k · hx)
  simp_rw [pow_mul]
  apply summable_geometric_of_lt_one (by simp)
  exact (pow_lt_one_iff_of_nonneg (by simp) (by simp)).mpr hx

lemma tsum_pow_mul_prod_bound (k : ℕ) {x : R} (hx : ‖x‖ < 1) :
    ‖∑' n, x ^ ((k + 1) * n) * ∏ i ∈ range (n + 1), (1 - x ^ (k + i + 1))‖ ≤
      (1 - ‖x‖)⁻¹ * ∏' i, (1 + ‖x‖ ^ i) := by
  refine tsum_of_norm_bounded (g := fun n ↦ ‖x‖ ^ n * ∏' i, (1 + ‖x‖ ^ i)) ?_ fun n ↦ ?_
  · rw [← tsum_geometric_of_lt_one (by simp) hx]
    exact (summable_geometric_of_lt_one (by simp) hx).hasSum.mul_right _
  · apply (pow_mul_prod_bound k n hx).trans
    gcongr ?_ * ?_
    · exact tprod_nonneg fun _ ↦ by positivity
    · grind [mul_comm, pow_mul, pow_le_of_le_one (by simp) (pow_le_one₀ (by simp) hx.le)]

lemma multipliable_one_sub_pow_add [CompleteSpace R] (k : ℕ) {x : R} (hx : ‖x‖ < 1) :
    Multipliable (fun n ↦ 1 - x ^ (n + k + 1)) := by
  apply multipliable_one_sub_of_summable
  apply Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun n ↦ norm_pow_le _ _)
  simp_rw [pow_add]
  exact ((summable_geometric_of_lt_one (by simp) hx).mul_right _).mul_right _

end Pentagonal

public section

/-- The Euler function $\phi(x) = \sum_{k=-\infty}^{\infty}(-1)^k x^{k (3k - 1) / 2}$, defined
as a power series with the same coefficients as `PowerSeries.pentagonalSeries`. See
`eulerFunction_eq_tsum_pentagonal` for the expression using pentagonal numbers. -/
noncomputable def eulerFunction (x : R) : R :=
  ∑' n, (PowerSeries.pentagonalSeries R).coeff n * x ^ n

omit [NormOneClass R] in
theorem eulerFunction_def (x : R) :
    eulerFunction x = ∑' n, (PowerSeries.pentagonalSeries R).coeff n * x ^ n := by
  rfl

omit [NormOneClass R] in
theorem eulerFunction_eq_tsum_pentagonal (x : R) :
    eulerFunction x = ∑' k, k.negOnePow * x ^ pentagonal k := by
  simp [eulerFunction, PowerSeries.coeff_pentagonalSeries_mul_eq_extend, pentagonal_injective]

variable [CompleteSpace R]

theorem hasSum_eulerFunction_pentagonalSeries {x : R} (hx : ‖x‖ < 1) :
    HasSum (fun n ↦ (PowerSeries.pentagonalSeries R).coeff n * x ^ n) (eulerFunction x) := by
  refine (Summable.hasSum_iff ?_).mpr rfl
  refine (summable_geometric_of_lt_one (norm_nonneg x) hx).of_norm_bounded fun n ↦ ?_
  by_cases hn : n ∈ Set.range pentagonal
  · obtain ⟨k, rfl⟩ := hn
    rw [PowerSeries.coeff_pentagonalSeries_pentagonal, Int.coe_negOnePow]
    grw [norm_mul_le, norm_pow_le, norm_pow_le]
    simp
  · simp [PowerSeries.coeff_pentagonalSeries_eq_zero R hn]

theorem hasSum_eulerFunction_pentagonal {x : R} (hx : ‖x‖ < 1) :
    HasSum (fun k ↦ k.negOnePow * x ^ pentagonal k) (eulerFunction x) := by
  simpa [pentagonal_injective, PowerSeries.coeff_pentagonalSeries_mul_eq_extend] using
    hasSum_eulerFunction_pentagonalSeries hx

theorem hasSum_eulerFunction_pentagonal_pair {x : R} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦ (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)))
      (eulerFunction x) := by
  have h := hasSum_eulerFunction_pentagonal hx
  rw [← neg_injective.hasSum_iff (by simp [neg_involutive.surjective.range_eq])] at h
  convert h.nat_add_neg_add_one with k
  simp [-Int.coe_negOnePow, Int.negOnePow_add, Int.coe_negOnePow_natCast]
  ring

theorem eulerFunction_eq_tsum_pentagonal_pair {x : R} (hx : ‖x‖ < 1) :
    eulerFunction x = ∑' k : ℕ, (-1) ^ k * (x ^ pentagonal (-k) - x ^ pentagonal (k + 1)) :=
  (hasSum_eulerFunction_pentagonal_pair hx).tsum_eq.symm

/-- **Pentagonal number theorem** for Euler function, expressed as an infinite product.
See `eulerFunction_eq_tsum_pentagonal` that expresses `eulerFunction` as an infinite sum. -/
theorem eulerFunction_eq_tprod {x : R} (hx : ‖x‖ < 1) :
    eulerFunction x = ∏' n : ℕ, (1 - x ^ (n + 1)) := by
  rw [eulerFunction_eq_tsum_pentagonal_pair hx]
  refine (Pentagonal.tprod_one_sub_pow ?_ ?_ ?_ ?_ ?_).symm
  · exact tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx
  · exact fun k ↦ (Pentagonal.summable_norm_pow_mul_prod k hx).of_norm
  · exact (Pentagonal.multipliable_one_sub_pow_add · hx)
  · exact (hasSum_eulerFunction_pentagonal_pair hx).summable
  · apply Tendsto.zero_mul_isBoundedUnder_le
    · refine isBoundedUnder_le_mul_tendsto_zero ⟨1, by simp⟩ ?_
      apply (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hx).comp
      rw [tendsto_atTop_atTop]
      exact fun k ↦ ⟨k, fun n hn ↦ hn.trans (by grind)⟩
    · exact isBoundedUnder_of ⟨_, fun k ↦ Pentagonal.tsum_pow_mul_prod_bound k hx⟩

/-- **Pentagonal number theorem** for Euler function, expressed as an infinite product.
See `hasSum_eulerFunction_pentagonal` that expresses `eulerFunction` as an infinite sum. -/
theorem hasProd_eulerFunction {x : R} (hx : ‖x‖ < 1) :
    HasProd (fun n ↦ 1 - x ^ (n + 1)) (eulerFunction x) := by
  refine (Multipliable.hasProd_iff ?_).mpr (eulerFunction_eq_tprod hx).symm
  simpa using Pentagonal.multipliable_one_sub_pow_add 0 hx

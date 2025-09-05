/-
Copyright (c) 2025 Geoffrey Irving. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Irving
-/

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric

/-!
# Taylor series bounds for trigonometric functions

## Main statements

We prove Taylor series bounds with optimal remainder for `sin` and `cos`, over both `ℂ` and `ℝ`.
See `Mathlib/Analysis/SpecialFunctions/Trigonometric/Bounds.lean` for simpler inequalities and
monotonicity in various intervals, and `Mathlib/Analysis/SpecialFunctions/Trigonometric/Basic.lean`
for even simpler inequalities and monotonicity results.

## Tags

sin, cos
-/

open Set
open scoped Real

lemma Complex.sin_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) (n : ℕ) :
    ‖sin z - z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial‖ ≤
      ‖z‖ ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have e : z * ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k + 1).factorial =
      (∑ k ∈ Finset.range (2 * n + 1), (-z * I) ^ k / k.factorial -
       ∑ k ∈ Finset.range (2 * n + 1), (z * I) ^ k / k.factorial) * I / 2 := by
    simp only [← Finset.sum_sub_distrib, ← sub_div, Finset.sum_range_even n, Finset.sum_div,
      Finset.mul_sum, Finset.sum_mul]
    simp only [Finset.sum_range_succ', pow_zero, Nat.factorial_zero, sub_self, zero_div, add_zero,
      zero_mul]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Nat.even_or_odd' k with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, pow_mul, pow_succ', pow_zero, mul_one, mul_pow,
        neg_mul, mul_neg, neg_neg]
      ring_nf
      simp only [mul_comm _ 2, pow_mul, I_sq, mul_neg]
      simp only [neg_mul, neg_neg, mul_one]
    · simp [e, pow_mul, pow_add, mul_pow]
  rw [sin, e, ← sub_div, ← sub_mul, sub_sub_sub_comm, norm_div, Complex.norm_two,
    div_le_iff₀ (by norm_num), norm_mul, Complex.norm_I, mul_one]
  refine le_trans (norm_sub_le _ _) ?_
  refine le_trans (add_le_add (Complex.exp_bound (x := -z * I) (by simpa) (by omega))
    (Complex.exp_bound (x := z * I) (by simpa) (by omega))) (le_of_eq ?_)
  simp only [norm_mul, Complex.norm_I, norm_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma Complex.cos_series_bound {z : ℂ} (z1 : ‖z‖ ≤ 1) {n : ℕ} (n0 : 0 < n) :
    ‖cos z - ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial‖ ≤
      ‖z‖ ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have e : ∑ k ∈ Finset.range n, (-1) ^ k * z ^ (2 * k) / (2 * k).factorial =
      (∑ k ∈ Finset.range (2 * n), (z * I) ^ k / k.factorial +
       ∑ k ∈ Finset.range (2 * n), (-z * I) ^ k / k.factorial) / 2 := by
    simp only [← Finset.sum_add_distrib, Finset.sum_range_even n, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rcases Nat.even_or_odd' k with ⟨a, e | e⟩
    · simp only [e, even_two, Even.mul_right, ↓reduceIte, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, mul_div_cancel_left₀, pow_mul, mul_pow, I_sq, mul_neg, mul_one, neg_mul,
        Even.neg_pow, ← add_div, neg_pow' (z ^ 2), mul_comm _ ((-1 : ℂ) ^ a), ← add_mul]
      ring
    · simp [e, pow_mul, pow_add, mul_pow, neg_div]
  rw [cos, e, ← sub_div, add_sub_add_comm, norm_div, Complex.norm_two, div_le_iff₀ (by norm_num)]
  refine le_trans (norm_add_le _ _) ?_
  refine le_trans (add_le_add (Complex.exp_bound (x := z * I) (by simpa) (by omega))
    (Complex.exp_bound (x := -z * I) (by simpa) (by omega))) (le_of_eq ?_)
  simp only [norm_mul, Complex.norm_I, norm_neg, Nat.succ_eq_add_one,
    Nat.cast_add, Nat.cast_mul]
  ring_nf

lemma Real.sin_series_bound {x : ℝ} (x1 : |x| ≤ 1) (n : ℕ) :
    |sin x - x * ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k + 1).factorial| ≤
      |x| ^ (2 * n + 1) * ((2 * n + 2) / ((2 * n + 1).factorial * (2 * n + 1))) := by
  have b := Complex.sin_series_bound (z := x) (by simpa only [Complex.norm_real]) n
  convert b <;> norm_cast

lemma Real.cos_series_bound {x : ℝ} (x1 : |x| ≤ 1) {n : ℕ} (n0 : 0 < n) :
    |cos x - ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) / (2 * k).factorial| ≤
      |x| ^ (2 * n) * ((2 * n + 1) / ((2 * n).factorial * (2 * n))) := by
  have b := Complex.cos_series_bound (z := x) (by simpa only [Complex.norm_real]) n0
  convert b <;> norm_cast

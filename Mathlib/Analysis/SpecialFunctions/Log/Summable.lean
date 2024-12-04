/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.NormedSpace.FunctionSeries

/-!
# Summable logs

We give conditions under which the logarithms of a summble sequence is summable. We also give some
results about when the sums converge uniformly.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Classical Complex

lemma Complex.log_of_summable {f : ℕ → ℂ} (hf : Summable f) :
    Summable (fun n : ℕ => Complex.log (1 + f n)) := by
  have hff := Summable.const_smul ((3 : ℝ) / 2) (summable_norm_iff.mpr hf)
  have := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero ((summable_norm_iff.mpr hf)))
  apply Summable.of_norm_bounded_eventually_nat (fun n => 3/2 * Complex.abs (f n)) hff
  simp only [smul_eq_mul, gt_iff_lt, ge_iff_le, dist_zero_right, Real.norm_eq_abs, Complex.abs_abs,
    Complex.norm_eq_abs, eventually_atTop] at *
  obtain ⟨n, hn⟩ := this (1/2) (one_half_pos)
  exact Exists.intro n fun m hm ↦ norm_log_one_add_half_le_self (LT.lt.le (hn m hm))

lemma Real.log_of_summable {f : ℕ → ℝ} (hf : Summable f) :
    Summable (fun n : ℕ => Real.log (1 + |f n|)) := by
  apply Summable.of_norm_bounded_eventually_nat (fun n => |f n|)
    (by apply summable_norm_iff.mpr hf)
  simp only [gt_iff_lt, ge_iff_le, norm_eq_abs, dist_zero_right, _root_.abs_abs,
    eventually_atTop]
  obtain ⟨n, _⟩ := Metric.tendsto_atTop.mp
    (Summable.tendsto_atTop_zero ((summable_norm_iff.mpr hf))) (1/2) (one_half_pos)
  refine ⟨n, fun m _ => ?_⟩
  have ht : 0 < 1 + |f m| := by
    exact Eq.mpr ((congrArg (fun _a ↦ 0 < _a) (add_comm 1 |f m|)))
        (add_pos_of_nonneg_of_pos (abs_nonneg (f m)) Real.zero_lt_one)
  have := Real.log_le_sub_one_of_pos ht
  rw [add_sub_cancel_left] at this
  apply le_trans _ this
  apply le_of_eq
  rw [abs_eq_self]
  apply Real.log_nonneg
  simp only [le_add_iff_nonneg_right, abs_nonneg]

lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n ≠ 0) : Multipliable (fun n : ℕ => 1 + f n) := by
  obtain ⟨a, ha⟩ := log_of_summable hf
  have := Filter.Tendsto.cexp ha
  have h1 : (fun n : Finset ℕ ↦ cexp (∑ x ∈ n, Complex.log (1 + f x))) =
     (fun n : Finset ℕ ↦ (∏ x ∈ n, (1 + f x))) := by
    ext y
    rw [Complex.exp_sum]
    congr
    exact funext fun r ↦ exp_log (hff r)
  exact Exists.intro (cexp a) (Eq.mp (congrArg (fun _a ↦ Tendsto _a atTop (𝓝 (cexp a))) h1) this)

lemma Real.summable_nat_multipliable_one_add (f : ℕ → ℝ) (hf : Summable f) :
    Multipliable (fun n : ℕ => 1 + |f n|) := by
  obtain ⟨a, ha⟩ := log_of_summable hf
  have := Filter.Tendsto.rexp ha
  have h1 : (fun n : Finset ℕ ↦ rexp (∑ x ∈ n, Real.log (1 + |f x|))) =
     (fun n : Finset ℕ ↦ (∏ x ∈ n, (1 + |f x|))) := by
    ext y
    rw [Real.exp_sum]
    congr
    exact funext fun r ↦ exp_log (add_pos_of_pos_of_nonneg Real.zero_lt_one (abs_nonneg (f r)))
  exact Exists.intro (rexp a) (Eq.mp (congrArg (fun _a ↦ Tendsto _a atTop (𝓝 (rexp a))) h1) this)

lemma Complex.tendstoUniformlyOn_tsum_nat_log_one_add {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ n x, x ∈ K → ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun n : ℕ => fun a : α => ∑ i in Finset.range n,
    (Complex.log (1 + f i a))) (fun a => ∑' i : ℕ, Complex.log (1 + f i a)) atTop K := by
  apply tendstoUniformlyOn_tsum_nat_eventually (hu.mul_left (3/2))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero hu) (1/2) (one_half_pos)
  simp only [Complex.norm_eq_abs, eventually_atTop, ge_iff_le]
  refine ⟨N, fun n hn x hx => ?_⟩
  apply le_trans (Complex.norm_log_one_add_half_le_self (z :=(f n x)) ?_)
  · simp only [Complex.norm_eq_abs, Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_left]
    apply h _ _ hx
  · apply le_trans (le_trans (h n x hx) (by simpa using Real.le_norm_self (u n))) (hN n hn).le

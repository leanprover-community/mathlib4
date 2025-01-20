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
     Summable (fun n : ℕ => log (1 + |f n|)) := by
  have : Summable (fun n ↦ Complex.ofRealCLM (log (1 + |f n|))) := by
    convert Complex.log_of_summable (Complex.ofRealCLM.summable hf.norm) with x
    rw [ofRealCLM_apply, ofReal_log (by positivity)]
    simp only [ofReal_add, ofReal_one, norm_eq_abs, ofRealCLM_apply]
  convert Complex.reCLM.summable this

lemma Complex.summable_nat_multipliable_one_add (f : ℕ → ℂ) (hf : Summable f)
    (hff : ∀ n : ℕ, 1 + f n ≠ 0) : Multipliable (fun n : ℕ => 1 + f n) := by
  refine Complex.summable_multipliable (fun n => 1 + f n) (by simpa) ?_
  simpa only [forall_const] using Complex.log_of_summable hf

lemma Real.summable_nat_multipliable_one_add (f : ℕ → ℝ) (hf : Summable f) :
    Multipliable (fun n : ℕ => 1 + |f n|) := by
  refine Real.summable_multipliable (fun n => 1 + |f n|) (fun _ ↦ by positivity) ?_
  simpa only [forall_const] using Real.log_of_summable hf

lemma Complex.tendstoUniformlyOn_tsum_nat_log_one_add {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun (n : ℕ) (a : α) => ∑ i in Finset.range n,
    (Complex.log (1 + f i a))) (fun a => ∑' i : ℕ, Complex.log (1 + f i a)) atTop K := by
  apply tendstoUniformlyOn_tsum_nat_eventually (hu.mul_left (3/2))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero hu) (1/2) (one_half_pos)
  simp only [Complex.norm_eq_abs, eventually_atTop, ge_iff_le] at *
  obtain ⟨N2, hN2⟩ := h
  refine ⟨max N N2, fun n hn x hx => ?_⟩
  apply le_trans (Complex.norm_log_one_add_half_le_self (z := (f n x)) ?_)
  · simp only [Complex.norm_eq_abs, Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_left]
    exact hN2 n (le_of_max_le_right hn) x hx
  · apply le_trans (le_trans (hN2 n (le_of_max_le_right hn) x hx)
    (by simpa using Real.le_norm_self (u n))) (hN n (le_of_max_le_left hn)).le

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

TODO: Generalise the indexing set from ℕ to some arbitrary type, but this needs
Summable.tendsto_atTop_zero to first be done. Also remove hff from
`Complex.multipliable_one_add_of_summable` once we have vanishing/non-vanishing results for infinite
products.

-/

open Filter Function Complex Real

open scoped Interval Topology BigOperators Nat Complex

variable {ι : Type*}

lemma Complex.summable_log_one_add_of_summable {f : ι → ℂ} (hf : Summable f) :
    Summable (fun i : ι => Complex.log (1 + f i)) := by
  apply (hf.norm.const_smul (3 / 2 : ℝ)).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
  exact norm_log_one_add_half_le_self hi

lemma Real.summable_log_one_add_of_summable {f : ι → ℝ} (hf : Summable f) :
     Summable (fun i : ι => log (1 + |f i|)) := by
  have : Summable (fun n ↦ Complex.ofRealCLM (log (1 + |f n|))) := by
    convert Complex.summable_log_one_add_of_summable (Complex.ofRealCLM.summable hf.norm) with x
    rw [ofRealCLM_apply, ofReal_log (by positivity)]
    simp only [ofReal_add, ofReal_one, norm_eq_abs, ofRealCLM_apply]
  convert Complex.reCLM.summable this

lemma Complex.multipliable_one_add_of_summable (f : ι → ℂ) (hf : Summable f)
    (hff : ∀ n : ι, 1 + f n ≠ 0) : Multipliable (fun n : ι => 1 + f n) := by
  refine Complex.multipliable_of_summable_log (fun n => 1 + f n) (by simpa) ?_
  simpa only [forall_const] using Complex.summable_log_one_add_of_summable hf

lemma Real.multipliable_one_add_of_summable (f : ι → ℝ) (hf : Summable f) :
    Multipliable (fun n : ι => 1 + |f n|) := by
  refine Real.multipliable_of_summable_log (fun n => 1 + |f n|) (fun _ ↦ by positivity) ?_
  simpa only [forall_const] using Real.summable_log_one_add_of_summable  hf

lemma Complex.tendstoUniformlyOn_tsum_nat_log_one_add {α : Type*} {f : ℕ → α → ℂ} (K : Set α)
    {u : ℕ → ℝ} (hu : Summable u) (h : ∀ᶠ n in atTop, ∀ x ∈ K, ‖f n x‖ ≤ u n) :
    TendstoUniformlyOn (fun (n : ℕ) (a : α) => ∑ i ∈ Finset.range n,
    (Complex.log (1 + f i a))) (fun a => ∑' i : ℕ, Complex.log (1 + f i a)) atTop K := by
  apply tendstoUniformlyOn_tsum_nat_eventually (hu.mul_left (3/2))
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (Summable.tendsto_atTop_zero hu) (1/2) (one_half_pos)
  simp only [eventually_atTop, ge_iff_le] at *
  obtain ⟨N2, hN2⟩ := h
  refine ⟨max N N2, fun n hn x hx => ?_⟩
  apply le_trans (Complex.norm_log_one_add_half_le_self (z := (f n x)) ?_)
  · simp only [Nat.ofNat_pos, div_pos_iff_of_pos_left, mul_le_mul_left]
    exact hN2 n (le_of_max_le_right hn) x hx
  · apply le_trans (le_trans (hN2 n (le_of_max_le_right hn) x hx)
    (by simpa using Real.le_norm_self (u n))) (hN n (le_of_max_le_left hn)).le

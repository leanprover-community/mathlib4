/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.NormedSpace.FunctionSeries

/-!
# Summability of logarithms

We give conditions under which the logarithms of a summble sequence is summable. We also give some
results about when the sums converge uniformly.

TODO: Remove hff from `Complex.multipliable_one_add_of_summable` once we have
vanishing/non-vanishing results for infinite products.

-/

variable {ι : Type*}

open Filter

section move_this_elsewhere
variable {G : Type*} [CommMonoidWithZero G] [TopologicalSpace G] {f : ι → G}

lemma hasProd_zero_of_exists_eq_zero (hf : ∃ i, f i = 0) : HasProd f 0 := by
  obtain ⟨i, hi⟩ := hf
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop {i}] with s hs
  refine (Finset.prod_eq_zero (Finset.singleton_subset_iff.mp hs) hi).symm

lemma multipliable_of_exists_eq_zero (hf : ∃ i, f i = 0) : Multipliable f :=
  ⟨0, hasProd_zero_of_exists_eq_zero hf⟩

open Finset in
lemma Multipliable.congr_cofinite' {R : Type*} [NormedField R]
    {f g : ι → R} (hf : Multipliable f) (hf' : ∀ i, f i ≠ 0)
    (hfg : ∀ᶠ i in cofinite, f i = g i) : Multipliable g := by
  classical
  obtain ⟨a, ha⟩ := hf
  obtain ⟨s, hs⟩ : ∃ s : Finset ι, ∀ i ∉ s, f i = g i :=
    ⟨hfg.toFinset, by simp only [Set.Finite.mem_toFinset, Set.mem_compl_iff, Set.mem_setOf_eq,
      Decidable.not_not, imp_self, implies_true]⟩
  refine ⟨_, (Tendsto.mul_const ((∏ i ∈ s, g i) / ∏ i ∈ s, f i) ha).congr' ?_⟩
  filter_upwards [eventually_ge_atTop s] with t ht
  calc (∏ i ∈ t, f i) * ((∏ i ∈ s, g i) / ∏ i ∈ s, f i)
  _ = ((∏ i ∈ s, f i) * ∏ i ∈ t \ s, g i) * _ := by
    conv_lhs => rw [← union_sdiff_of_subset ht, prod_union disjoint_sdiff,
      prod_congr rfl fun i hi ↦ hs i (mem_sdiff.mp hi).2]
  _ = ((∏ i ∈ s, f i) / ∏ i ∈ s, f i) * ((∏ i ∈ s, g i) * ∏ i ∈ t \ s, g i) := by ring
  _ = ∏ i ∈ t, g i := by
    rw [div_self, one_mul, ← prod_union disjoint_sdiff, union_sdiff_of_subset ht]
    exact prod_ne_zero_iff.mpr fun i _ ↦ hf' i

end move_this_elsewhere

namespace Complex
variable {f : ι → ℂ} {a : ℂ}

lemma hasProd_of_hasSum_log (hfn : ∀ i, f i ≠ 0) (hf : HasSum (fun i ↦ log (f i)) a) :
    HasProd f (exp a) :=
  hf.cexp.congr (by simp [exp_log, hfn])

lemma multipliable_of_summable_log (hfn : ∀ n, f n ≠ 0) (hf : Summable fun i ↦ log (f i)) :
    Multipliable f :=
  ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/-- Alternate verson of `Complex.multipliable_of_summable_log` assuming only that the terms are
eventually non-zero. -/
lemma multipliable_of_summable_log' (hfn : ∀ᶠ i in cofinite, f i ≠ 0)
    (hf : Summable fun i ↦ log (f i)) : Multipliable f := by
  have : Summable fun i ↦ log (if f i ≠ 0 then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i ↦ if f i ≠ 0 then f i else 1 := by
    refine multipliable_of_summable_log (fun i ↦ ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite' (fun i ↦ ?_) ?_
  · split_ifs with h <;> simp [h]
  · filter_upwards [hfn] with i hi using by simp [hi]

/-- The exponential of a convergent sum of complex logs is the corresponding infinite product. -/
lemma cexp_tsum_eq_tprod (hfn : ∀ i, f i ≠ 0) (hf : Summable fun i ↦ log (f i)) :
    cexp (∑' i, log (f i)) = ∏' i, f i  :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

lemma summable_log_one_add_of_summable {f : ι → ℂ} (hf : Summable f) :
    Summable (fun i ↦ log (1 + f i)) := by
  apply (hf.norm.mul_left _).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    using norm_log_one_add_half_le_self hi

lemma multipliable_one_add_of_summable (f : ι → ℂ) (hf : Summable f) :
    Multipliable (fun i ↦ 1 + f i) := by
  by_cases hff : ∃ i, 1 + f i = 0
  · exact (hasProd_zero_of_exists_eq_zero hff).multipliable
  · exact multipliable_of_summable_log (by simpa using hff) (summable_log_one_add_of_summable hf)

end Complex

namespace Real
variable {f : ι → ℝ} {a : ℝ}

lemma hasProd_of_hasSum_log (hfn : ∀ i, 0 < f i) (hf : HasSum (fun i ↦ log (f i)) a) :
    HasProd f (rexp a) :=
  hf.rexp.congr (by simp [exp_log, hfn])

lemma multipliable_of_summable_log (hfn : ∀ i, 0 < f i) (hf : Summable fun i ↦ log (f i)) :
    Multipliable f :=
  ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/-- Alternate verson of `Real.multipliable_of_summable_log` assuming only that positivity holds
eventually. -/
lemma multipliable_of_summable_log' (hfn : ∀ᶠ i in cofinite, 0 < f i)
    (hf : Summable fun i ↦ log (f i)) : Multipliable f := by
  have : Summable fun i ↦ log (if 0 < f i then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i ↦ if 0 < f i then f i else 1 := by
    refine multipliable_of_summable_log (fun i ↦ ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite' (fun i ↦ ?_) ?_
  · split_ifs with h <;> simp [h, ne_of_gt]
  · filter_upwards [hfn] with i hi using by simp [hi]

/-- The exponential of a convergent sum of real logs is the corresponding infinite product. -/
lemma rexp_tsum_eq_tprod (hfn : ∀ i, 0 < f i) (hf : Summable fun i ↦ log (f i)) :
    rexp (∑' i, log (f i)) = ∏' i, f i :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

open Complex in
lemma summable_log_one_add_of_summable (hf : Summable f) :
    Summable (fun i ↦ log (1 + f i)) := by
  rw [← summable_ofReal]
  apply (Complex.summable_log_one_add_of_summable (summable_ofReal.mpr hf)).congr_cofinite
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_le neg_one_lt_zero] with i hi
  rw [ofReal_log, ofReal_add, ofReal_one]
  linarith

example (hf : Summable f) : Summable (fun i ↦ log (1 + |f i|)) :=
  summable_log_one_add_of_summable hf.norm

lemma multipliable_one_add_of_summable (hf : Summable f) : Multipliable (fun i ↦ 1 + f i) := by
  refine multipliable_of_summable_log' ?_ (summable_log_one_add_of_summable hf)
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_lt neg_one_lt_zero] with i hi
  linarith

end Real

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

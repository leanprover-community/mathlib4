/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Topology.Algebra.InfiniteSum.Field

/-!
# Summability of logarithms

We give conditions under which the logarithms of a summble sequence is summable. We also use this
to relate summability of `f` to multipliability of `1 + f`.

-/

variable {ι : Type*}

open Filter Topology NNReal SummationFilter

namespace Complex
variable {f : ι → ℂ} {a : ℂ}

lemma hasProd_of_hasSum_log (hfn : ∀ i, f i ≠ 0) (hf : HasSum (fun i ↦ log (f i)) a) :
    HasProd f (exp a) :=
  hf.cexp.congr (by simp [exp_log, hfn])

lemma multipliable_of_summable_log (hf : Summable fun i ↦ log (f i)) :
    Multipliable f := by
  by_cases! hfn : ∃ n, f n = 0
  · exact multipliable_of_exists_eq_zero hfn
  · exact ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/-- The exponential of a convergent sum of complex logs is the corresponding infinite product. -/
lemma cexp_tsum_eq_tprod (hfn : ∀ i, f i ≠ 0) (hf : Summable fun i ↦ log (f i)) :
    cexp (∑' i, log (f i)) = ∏' i, f i :=
  (hasProd_of_hasSum_log hfn hf.hasSum).tprod_eq.symm

lemma summable_log_one_add_of_summable {f : ι → ℂ} (hf : Summable f) :
    Summable (fun i ↦ log (1 + f i)) := by
  apply (hf.norm.mul_left (3 / 2)).of_norm_bounded_eventually
  filter_upwards [hf.norm.tendsto_cofinite_zero.eventually_le_const one_half_pos] with i hi
    using norm_log_one_add_half_le_self hi

protected lemma multipliable_one_add_of_summable (hf : Summable f) :
    Multipliable (fun i ↦ 1 + f i) :=
  multipliable_of_summable_log (summable_log_one_add_of_summable hf)

end Complex

namespace Real
variable {f : ι → ℝ} {a : ℝ}

lemma hasProd_of_hasSum_log (hfn : ∀ i, 0 < f i) (hf : HasSum (fun i ↦ log (f i)) a) :
    HasProd f (rexp a) :=
  hf.rexp.congr (by simp [exp_log, hfn])

lemma multipliable_of_summable_log (hfn : ∀ i, 0 < f i) (hf : Summable fun i ↦ log (f i)) :
    Multipliable f :=
  ⟨_, hasProd_of_hasSum_log hfn hf.hasSum⟩

/-- Alternate version of `Real.multipliable_of_summable_log` assuming only that positivity holds
eventually. -/
lemma multipliable_of_summable_log' (hfn : ∀ᶠ i in cofinite, 0 < f i)
    (hf : Summable fun i ↦ log (f i)) : Multipliable f := by
  have : Summable fun i ↦ log (if 0 < f i then f i else 1) := by
    apply hf.congr_cofinite
    filter_upwards [hfn] with i hi using by simp [hi]
  have : Multipliable fun i ↦ if 0 < f i then f i else 1 := by
    refine multipliable_of_summable_log (fun i ↦ ?_) this
    split_ifs with h <;> simp [h]
  refine this.congr_cofinite₀ (fun i ↦ ?_) ?_
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

protected lemma multipliable_one_add_of_summable (hf : Summable f) :
    Multipliable (fun i ↦ 1 + f i) := by
  refine multipliable_of_summable_log' ?_ (summable_log_one_add_of_summable hf)
  filter_upwards [hf.tendsto_cofinite_zero.eventually_const_lt neg_one_lt_zero] with i hi
  linarith

end Real

section NormedRing

lemma Multipliable.eventually_bounded_finset_prod {v : ι → ℝ} (hv : Multipliable v) :
    ∃ r₁ > 0, ∃ s₁, ∀ t, s₁ ⊆ t → ∏ i ∈ t, v i ≤ r₁ := by
  obtain ⟨r₁, hr₁⟩ := exists_gt (max 0 <| ∏' i, v i)
  rw [max_lt_iff] at hr₁
  have := hv.hasProd.eventually_le_const hr₁.2
  rw [unconditional, eventually_atTop] at this
  exact ⟨r₁, hr₁.1, this⟩

variable {R : Type*} [NormedCommRing R] [NormOneClass R] {f : ι → R}

lemma multipliable_norm_one_add_of_summable_norm (hf : Summable fun i ↦ ‖f i‖) :
    Multipliable fun i ↦ ‖1 + f i‖ := by
  conv => enter [1, i]; rw [← sub_add_cancel ‖1 + f i‖ 1, add_comm]
  refine Real.multipliable_one_add_of_summable <| hf.of_norm_bounded (fun i ↦ ?_)
  simpa using abs_norm_sub_norm_le (1 + f i) 1

lemma Finset.norm_prod_one_add_sub_one_le (t : Finset ι) (f : ι → R) :
    ‖∏ i ∈ t, (1 + f i) - 1‖ ≤ Real.exp (∑ i ∈ t, ‖f i‖) - 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert x t hx IH =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx, Real.exp_add,
      show (1 + f x) * ∏ i ∈ t, (1 + f i) - 1 =
        (∏ i ∈ t, (1 + f i) - 1) + f x * ∏ x ∈ t, (1 + f x) by ring]
    refine (norm_add_le_of_le IH (norm_mul_le _ _)).trans ?_
    generalize h : Real.exp (∑ i ∈ t, ‖f i‖) = A at ⊢ IH
    rw [sub_add_eq_add_sub, sub_le_sub_iff_right]
    transitivity A + ‖f x‖ * A
    · grw [norm_le_norm_sub_add (∏ x ∈ t, (1 + f x)) 1, IH, norm_one, sub_add_cancel]
    rw [← one_add_mul, add_comm]
    exact mul_le_mul_of_nonneg_right (Real.add_one_le_exp _) (h ▸ Real.exp_nonneg _)

lemma prod_vanishing_of_summable_norm (hf : Summable fun i ↦ ‖f i‖) {ε : ℝ} (hε : 0 < ε) :
    ∃ s₂, ∀ t, Disjoint t s₂ → ‖∏ i ∈ t, (1 + f i) - 1‖ < ε := by
  suffices ∃ s, ∀ t, Disjoint t s → Real.exp (∑ i ∈ t, ‖f i‖) - 1 < ε from
    this.imp fun s hs t ht ↦ (t.norm_prod_one_add_sub_one_le _).trans_lt (hs t ht)
  suffices {x | Real.exp x - 1 < ε} ∈ 𝓝 0 from hf.vanishing this
  let f (x) := Real.exp x - 1
  have : Set.Iio ε ∈ nhds (f 0) := by simpa [f] using Iio_mem_nhds hε
  exact ContinuousAt.preimage_mem_nhds (by fun_prop) this

open Finset in
/-- In a complete normed ring, `∏' i, (1 + f i)` is convergent if the sum of real numbers
`∑' i, ‖f i‖` is convergent. -/
lemma multipliable_one_add_of_summable [CompleteSpace R]
    (hf : Summable fun i ↦ ‖f i‖) : Multipliable fun i ↦ (1 + f i) := by
  classical
  refine CompleteSpace.complete <| Metric.cauchy_iff.mpr ⟨by infer_instance, fun ε hε ↦ ?_⟩
  obtain ⟨r₁, hr₁, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hf).eventually_bounded_finset_prod
  obtain ⟨s₂, hs₂⟩ := prod_vanishing_of_summable_norm hf (show 0 < ε / (2 * r₁) by positivity)
  simp only [unconditional, Filter.mem_map, mem_atTop_sets, ge_iff_le, le_eq_subset,
    Set.mem_preimage]
  let s := s₁ ∪ s₂
  -- The idea here is that if `s` is a large enough finset, then the product over `s` is bounded
  -- by some `r`, and the product over finsets disjoint from `s` is within `ε / (2 * r)` of 1.
  -- From this it follows that the products over any two finsets containing `s` are within `ε` of
  -- each other.
  -- Here `s₁ ⊆ s` guarantees that the product over `s` is bounded, and `s₂ ⊆ s` guarantees that
  -- the product over terms not in `s` is small.
  refine ⟨Metric.ball (∏ i ∈ s, (1 + f i)) (ε / 2), ⟨s, fun b hb ↦ ?_⟩, ?_⟩
  · rw [← union_sdiff_of_subset hb, prod_union sdiff_disjoint.symm,
      Metric.mem_ball, dist_eq_norm_sub, ← mul_sub_one,
      show ε / 2 = r₁ * (ε / (2 * r₁)) by field_simp]
    apply (norm_mul_le _ _).trans_lt
    refine lt_of_le_of_lt (b := r₁ * ‖∏ x ∈ b \ s, (1 + f x) - 1‖) ?_ ?_
    · refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      exact (Finset.norm_prod_le _ _).trans (hs₁ _ subset_union_left)
    · refine mul_lt_mul_of_pos_left (hs₂ _ ?_) hr₁
      simp [s, sdiff_union_distrib, disjoint_iff_inter_eq_empty]
  · intro x hx y hy
    exact (dist_triangle_right _ _ (∏ i ∈ s, (1 + f i))).trans_lt (add_halves ε ▸ add_lt_add hx hy)

lemma Summable.summable_log_norm_one_add (hu : Summable fun n ↦ ‖f n‖) :
    Summable fun i ↦ Real.log ‖1 + f i‖ := by
  suffices Summable (‖1 + f ·‖ - 1) from
    (Real.summable_log_one_add_of_summable this).congr (by simp)
  refine .of_norm (hu.of_nonneg_of_le (fun i ↦ by positivity) fun i ↦ ?_)
  simp only [Real.norm_eq_abs, abs_le]
  constructor
  · simpa using norm_add_le (1 + f i) (-f i)
  · simpa [add_comm] using norm_add_le (f i) 1

lemma tprod_one_add_ne_zero_of_summable [CompleteSpace R] [NormMulClass R]
    (hf : ∀ i, 1 + f i ≠ 0)
    (hu : Summable (‖f ·‖)) : ∏' i : ι, (1 + f i) ≠ 0 := by
  rw [← norm_ne_zero_iff, Multipliable.norm_tprod]
  · rw [← Real.rexp_tsum_eq_tprod (fun i ↦ norm_pos_iff.mpr <| hf i) hu.summable_log_norm_one_add]
    apply Real.exp_ne_zero
  · exact multipliable_one_add_of_summable hu

end NormedRing

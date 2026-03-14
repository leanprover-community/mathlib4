/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Infinite products in normed rings

This file proves a dominated convergence theorem for infinite products of terms of the form
`(1 + f n k)` in a complete normed commutative ring.

## Main results

* `tendsto_tprod_one_add_of_dominated_convergence`: if `f n k → g k` pointwise and
  `‖f n k‖ ≤ bound k` eventually with `bound` summable, then
  `∏' k, (1 + f n k) → ∏' k, (1 + g k)`.
-/

open Topology Filter Metric Real Set

variable {α R β : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {g : β → R}
{bound : β → ℝ}

/-- Finite sub-products of the tail of `1 + g` are close to 1, lifted to the infinite tprod
via closedness of balls. -/
lemma norm_tprod_tail_sub_one_le {s : Finset β} {δ : ℝ}
    (h_sum : Summable bound) (h_bound : ∀ k, ‖g k‖ ≤ bound k)
    (hs_tail : ∀ t : Finset β, Disjoint t s → rexp (∑ k ∈ t, bound k) - 1 < δ) :
    ‖(∏' k : {k // k ∉ s}, (1 + g k)) - 1‖ ≤ δ := by
  have hfinprod : ∀ t : Finset {k // k ∉ s},
      ‖∏ i ∈ t, (1 + g i) - 1‖ ≤ δ := fun t ↦
    (((t.norm_prod_one_add_sub_one_le _).trans (sub_le_sub_right (Real.exp_le_exp.mpr
      (Finset.sum_le_sum (fun i _ ↦ by exact h_bound i))) 1)).trans_lt (by
        simpa using hs_tail (t.map ⟨Subtype.val, Subtype.val_injective⟩)
          (by simp [Finset.disjoint_left]; aesop))).le
  have hmem : ∏' k : {k // k ∉ s}, (1 + g k) ∈ Metric.closedBall (1 : R) δ :=
    Metric.isClosed_closedBall.mem_of_tendsto (multipliable_one_add_of_summable
      ((h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound).comp_injective
        Subtype.val_injective)).hasProd
      (by filter_upwards with t using by simpa [dist_eq_norm, norm_sub_rev] using hfinprod t)
  rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm, norm_sub_rev] at hmem

lemma eventually_dist_tprod_one_add_lt {𝓕 : Filter α} [NeBot 𝓕] {f : α → β → R}
    (h_sum : Summable bound) (h_bound_g : ∀ k, ‖g k‖ ≤ bound k)
    (hab : ∀ k, Tendsto (f · k) 𝓕 (nhds (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in 𝓕, dist (∏' k, (1 + f n k)) (∏' k, (1 + g k)) < ε := by
  classical
  have hsum_g : Summable (‖g ·‖) := h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound_g
  obtain ⟨r, hr, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hsum_g).eventually_bounded_finset_prod
  obtain ⟨s₂, hs₂⟩ := h_sum.vanishing
    (ContinuousAt.preimage_mem_nhds (by fun_prop : ContinuousAt (fun x : ℝ ↦ rexp x - 1) 0)
      (by simpa using Iio_mem_nhds (lt_min one_pos (by positivity : 0 < ε / (8 * r)))))
  let s := s₁ ∪ s₂
  have hs₂' : ∀ t, Disjoint t s → rexp (∑ k ∈ t, bound k) - 1 < min 1 (ε / (8 * r)) :=
    fun t ht ↦ hs₂ t (ht.mono_right Finset.subset_union_right)
  filter_upwards [h_bound, (tendsto_finset_prod s (fun k _ ↦ (hab k).const_add 1)).eventually
      (ball_mem_nhds _ (show (0 : ℝ) < ε / 4 by positivity))] with n hn hAn
  rw [dist_eq_norm, tprod_one_add_eq_finset_mul_compl hsum_g s,
    tprod_one_add_eq_finset_mul_compl (h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hn) s] at *
  calc ‖(∏ k ∈ s, (1 + f n k)) * _ - (∏ k ∈ s, (1 + g k)) * _‖
      ≤ ε / 4 * 2 + r * (2 * (ε / (8 * r))) := by
        refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
        gcongr
        · linarith [norm_le_norm_sub_add (∏' k : {k // k ∉ s}, (1 + f n k)) 1,
            norm_one (α := R), (norm_tprod_tail_sub_one_le h_sum hn hs₂').trans (min_le_left _ _)]
        · exact (Finset.norm_prod_le _ _).trans (hs₁ s Finset.subset_union_left)
        · set a := ∏' k : {k // k ∉ s}, (1 + f n k)
          set b := ∏' k : {k // k ∉ s}, (1 + g k)
          have : ‖a - b‖ ≤ ‖a - 1‖ + ‖b - 1‖ := by
            rw [show a - b = (a - 1) - (b - 1) by ring]
            exact norm_sub_le _ _
          linarith [(norm_tprod_tail_sub_one_le h_sum hn hs₂').trans (min_le_right 1 (ε / (8 * r))),
            (norm_tprod_tail_sub_one_le h_sum h_bound_g hs₂').trans (min_le_right 1 (ε / (8 * r)))]
    _ < ε := by field_simp; linarith

/-- Dominated convergence for infinite products: if `f n k → g k` pointwise and
`‖f n k‖ ≤ bound k` eventually with `bound` summable,
then `∏' k, (1 + f n k) → ∏' k, (1 + g k)`. -/
public theorem tendsto_tprod_one_add_of_dominated_convergence {𝓕 : Filter α} {f : α → β → R}
    (h_sum : Summable bound) (hab : ∀ k, Tendsto (f · k) 𝓕 (nhds (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∏' k, (1 + f n k)) 𝓕 (nhds (∏' k, (1 + g k))) := by
  rcases eq_or_neBot 𝓕 with rfl | _
  · simp
  have h_bound_g : ∀ k, ‖g k‖ ≤ bound k := fun k ↦
    le_of_tendsto ((hab k).norm) (h_bound.mono fun n hn ↦ hn k)
  exact Metric.tendsto_nhds.mpr fun ε hε ↦
    eventually_dist_tprod_one_add_lt h_sum h_bound_g hab h_bound hε

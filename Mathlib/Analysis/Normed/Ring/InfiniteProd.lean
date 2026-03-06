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
  have hfinprod : ∀ t : Finset {k // k ∉ s}, ‖∏ i ∈ t, (1 + g i) - 1‖ ≤ δ := by
    intro t; apply le_of_lt
    calc ‖∏ i ∈ t, (1 + g i) - 1‖
        ≤ rexp (∑ i ∈ t, ‖g i‖) - 1 := t.norm_prod_one_add_sub_one_le _
      _ ≤ rexp (∑ i ∈ t, bound i) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr
            (Finset.sum_le_sum (fun i _ ↦ by exact h_bound i))) 1
      _ < δ := by
          simpa using hs_tail (t.map ⟨Subtype.val, Subtype.val_injective⟩)
            (by simp [Finset.disjoint_left]; aesop)
  have hmem : ∏' k : {k // k ∉ s}, (1 + g k) ∈ Metric.closedBall (1 : R) δ :=
    Metric.isClosed_closedBall.mem_of_tendsto (multipliable_one_add_of_summable
      ((h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound).comp_injective
        Subtype.val_injective)).hasProd
      (by filter_upwards with t using by simpa [dist_eq_norm, norm_sub_rev] using hfinprod t)
  rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm, norm_sub_rev] at hmem

public theorem tendsto_tprod_one_add_of_dominated_convergence {𝓕 : Filter α} {f : α → β → R}
    (h_sum : Summable bound) (hab : ∀ k, Tendsto (f · k) 𝓕 (nhds (g k)))
    (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∏' k, (1 + f n k)) 𝓕 (nhds (∏' k, (1 + g k))) := by
  classical
  by_cases hbot : 𝓕 = ⊥
  · simp [hbot]
  have : NeBot 𝓕 := ⟨hbot⟩
  have h_bound_g : ∀ k, ‖g k‖ ≤ bound k := fun k ↦
    le_of_tendsto ((hab k).norm) (h_bound.mono fun n hn ↦ hn k)
  have hsum_g : Summable (‖g ·‖) := h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound_g
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨r, hr, s₁, hs₁⟩ :=
    (multipliable_norm_one_add_of_summable_norm hsum_g).eventually_bounded_finset_prod
  obtain ⟨s₂, hs₂⟩ := h_sum.vanishing
    (ContinuousAt.preimage_mem_nhds (by fun_prop : ContinuousAt (fun x : ℝ ↦ rexp x - 1) 0)
      (by simpa using Iio_mem_nhds (lt_min one_pos (by positivity : 0 < ε / (8 * r)))))
  let s := s₁ ∪ s₂
  have hs₂' : ∀ t, Disjoint t s → rexp (∑ k ∈ t, bound k) - 1 < min 1 (ε / (8 * r)) :=
    fun t ht ↦ hs₂ t (ht.mono_right Finset.subset_union_right)
  have hP_g : ∏' k, (1 + g k) = (∏ k ∈ s, (1 + g k)) * ∏' k : {k // k ∉ s}, (1 + g k) :=
    ((s.hasProd (fun k ↦ 1 + g k)).mul_compl (multipliable_one_add_of_summable
    (hsum_g.comp_injective Subtype.val_injective)).hasProd).tprod_eq
  have hBP_f : ∀ᶠ n in 𝓕, ‖(∏' k : {k // k ∉ s}, (1 + f n k)) - 1‖ ≤ min 1 (ε / (8 * r)) ∧
      ∏' k, (1 + f n k) = (∏ k ∈ s, (1 + f n k)) * ∏' k : {k // k ∉ s}, (1 + f n k) := by
    filter_upwards [h_bound] with n hn
    have hmn_compl : Multipliable (fun k : {k // k ∉ s} ↦ 1 + f n k) :=
      multipliable_one_add_of_summable
      ((h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hn).comp_injective Subtype.val_injective)
    exact ⟨norm_tprod_tail_sub_one_le h_sum hn hs₂',
      ((s.hasProd (fun k ↦ 1 + f n k)).mul_compl hmn_compl.hasProd).tprod_eq⟩
  filter_upwards [hBP_f,
    (tendsto_finset_prod s (fun k _ ↦ (hab k).const_add 1)).eventually
      (ball_mem_nhds _ (show (0 : ℝ) < ε / 4 by positivity))]
    with n ⟨hBn, hPn⟩ hAn
  rw [dist_eq_norm, hP_g, hPn] at *
  set B_n := ∏' k : {k // k ∉ s}, (1 + f n k)
  set B := ∏' k : {k // k ∉ s}, (1 + g k)
  have hBn_B : ‖B_n - B‖ ≤ ε / (4 * r) := by
    calc ‖B_n - B‖ = ‖(B_n - 1) - (B - 1)‖ := by congr 1; ring
      _ ≤ ‖B_n - 1‖ + ‖B - 1‖ := norm_sub_le _ _
      _ ≤ ε / (8 * r) + ε / (8 * r) := add_le_add (hBn.trans (min_le_right _ _))
            ((norm_tprod_tail_sub_one_le h_sum h_bound_g hs₂').trans (min_le_right _ _))
      _ = ε / (4 * r) := by ring
  calc ‖(∏ k ∈ s, (1 + f n k)) * B_n - (∏ k ∈ s, (1 + g k)) * B‖
      = ‖((∏ k ∈ s, (1 + f n k)) - ∏ k ∈ s, (1 + g k)) * B_n +
          (∏ k ∈ s, (1 + g k)) * (B_n - B)‖ := by ring_nf
    _ ≤ ‖(∏ k ∈ s, (1 + f n k)) - ∏ k ∈ s, (1 + g k)‖ * ‖B_n‖ +
          ‖∏ k ∈ s, (1 + g k)‖ * ‖B_n - B‖ := by
        refine (norm_add_le _ _).trans ?_; gcongr <;> exact norm_mul_le _ _
    _ ≤ ε / 4 * 2 + r * (ε / (4 * r)) := by
        gcongr
        · linarith [norm_le_norm_sub_add B_n 1, norm_one (α := R),
            hBn.trans (min_le_left _ _)]
        · exact (Finset.norm_prod_le _ _).trans (hs₁ s Finset.subset_union_left)
    _ < ε := by rw [show r * (ε / (4 * r)) = ε / 4 from by field_simp]; linarith

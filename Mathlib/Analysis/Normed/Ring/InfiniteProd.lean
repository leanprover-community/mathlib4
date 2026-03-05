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

open  Topology Filter Metric Real Set

variable {R β : Type*} [NormedCommRing R] [NormOneClass R] {g : β → R} {bound : β → ℝ}

lemma norm_tprod_tail_sub_one_le [CompleteSpace R] {s : Finset β} {δ : ℝ}
    (h_sum : Summable bound) (hh_bound : ∀ k, ‖g k‖ ≤ bound k)
    (hs_tail : ∀ t : Finset β, Disjoint t s → rexp (∑ k ∈ t, bound k) - 1 < δ) :
    ‖(∏' k : {k // k ∉ s}, (1 + g k)) - 1‖ ≤ δ := by
  have hfinprod : ∀ t : Finset {k // k ∉ s}, ‖∏ i ∈ t, (1 + g i) - 1‖ ≤ δ := by
    intro t
    calc ‖∏ i ∈ t, (1 + g i) - 1‖
        ≤ rexp (∑ i ∈ t, ‖g i‖) - 1 := t.norm_prod_one_add_sub_one_le _
      _ ≤ rexp (∑ i ∈ t, bound i) - 1 := sub_le_sub_right (Real.exp_le_exp.mpr
            (Finset.sum_le_sum (fun i _ ↦ by apply hh_bound i))) 1
      _ ≤ δ := by apply le_of_lt
                  simpa using hs_tail (t.map ⟨Subtype.val, Subtype.val_injective⟩)
                    (by simp [Finset.disjoint_left]; aesop);
  have hmulti_tail : Multipliable (fun k : {k // k ∉ s} ↦ 1 + g k) :=
    multipliable_one_add_of_summable ((h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
      hh_bound).comp_injective Subtype.val_injective)
  have hmem : ∏' k : {k // k ∉ s}, (1 + g k) ∈ Metric.closedBall (1 : R) δ := by
    apply Metric.isClosed_closedBall.mem_of_tendsto hmulti_tail.hasProd ?_
    filter_upwards with t using (by simpa [dist_eq_norm, norm_sub_rev] using hfinprod t)
  rwa [Metric.mem_closedBall, dist_comm, dist_eq_norm, norm_sub_rev] at hmem

lemma norm_head_prod_le_exp_tsum (s : Finset β)
    (hh_bound : ∀ k, ‖g k‖ ≤ bound k) (h_sum : Summable bound) :
    ‖∏ k ∈ s, (1 + g k)‖ ≤ rexp (∑' k, bound k) := by
  calc ‖∏ k ∈ s, (1 + g k)‖
      ≤ ‖∏ k ∈ s, (1 + g k) - 1‖ + 1 := by
        have := norm_add_le (∏ k ∈ s, (1 + g k) - 1) (1 : R)
        simp [sub_add_cancel] at this; grind
    _ ≤ (rexp (∑ k ∈ s, ‖g k‖) - 1) + 1 := by
        linarith [s.norm_prod_one_add_sub_one_le g]
    _ = rexp (∑ k ∈ s, ‖g k‖) := by ring
    _ ≤ rexp (∑' k, bound k) := by
        gcongr
        exact (Finset.sum_le_sum fun k _ ↦ hh_bound k).trans
          (h_sum.sum_le_tsum s (fun k _ ↦ le_trans (by grind) (hh_bound k)))

lemma tendsto_tprod_final_estimate_aux {A A_n B B_n : R} {ε C δ : ℝ}
    (hBn_close : ‖B_n - 1‖ ≤ δ) (hB_g : ‖B - 1‖ ≤ δ) (hAn_close : dist A_n A < ε / 4)
    (hδ_le_1 : δ ≤ 1) (hA_norm : ‖A‖ ≤ C) (hC_pos : 0 < C)
    (hε : ε = 4 * C * δ) : ‖A_n * B_n - A * B‖ < ε := by
  have hBn_norm : ‖B_n‖ ≤ 2 := by
    have h1 := norm_add_le (B_n - 1) (1 : R)
    rw [sub_add_cancel] at h1; linarith [norm_one (α := R)]
  have hBn_B : ‖B_n - B‖ ≤ 2 * δ := by
    have : B_n - B = (B_n - 1) - (B - 1) := by ring
    rw [this]; linarith [norm_sub_le (B_n - 1) (B - 1)]
  have key : A_n * B_n - A * B = (A_n - A) * B_n + A * (B_n - B) := by ring
  rw [key, dist_eq_norm] at *
  calc ‖(A_n - A) * B_n + A * (B_n - B)‖
      ≤ ‖(A_n - A) * B_n‖ + ‖A * (B_n - B)‖ := norm_add_le _ _
    _ ≤ ‖A_n - A‖ * ‖B_n‖ + ‖A‖ * ‖B_n - B‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
    _ ≤ ‖A_n - A‖ * 2 + C * (2 * δ) := by gcongr
    _ < ε / 4 * 2 + C * (2 * δ) := by linarith
    _ = ε := by subst hε; ring

public theorem tendsto_tprod_one_add_of_dominated_convergence
    {α : Type*} {𝓕 : Filter α} [CompleteSpace R] {f : α → β → R} (h_sum : Summable bound)
    (hab : ∀ k, Tendsto (f · k) 𝓕 (nhds (g k))) (h_bound : ∀ᶠ n in 𝓕, ∀ k, ‖f n k‖ ≤ bound k) :
    Tendsto (fun n ↦ ∏' k, (1 + f n k)) 𝓕 (nhds (∏' k, (1 + g k))) := by
  by_cases hbot : 𝓕 = ⊥
  · aesop
  have : NeBot 𝓕 := ⟨hbot⟩
  have h_bound_g : ∀ k, ‖g k‖ ≤ bound k := fun k ↦
    le_of_tendsto ((hab k).norm) (h_bound.mono fun n hn ↦ hn k)
  have hsum_g : Summable (‖g ·‖) := h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound_g
  rw [Metric.tendsto_nhds]
  intro ε εpos
  set C := rexp (∑' k, bound k)
  have hC_pos : 0 < C := Real.exp_pos _
  set δ := min 1 (ε / (4 * C))
  have hδ_pos : 0 < δ := lt_min one_pos (div_pos εpos (mul_pos (by grind) hC_pos))
  have hU : {x : ℝ | rexp x - 1 < δ} ∈ 𝓝 (0 : ℝ) := by
    have : Set.Iio δ ∈ 𝓝 ((fun x : ℝ ↦ rexp x - 1) 0) := by simpa using Iio_mem_nhds hδ_pos
    exact ContinuousAt.preimage_mem_nhds (Real.continuous_exp.continuousAt.sub continuousAt_const)
      this
  obtain ⟨s, hs_tail⟩ := h_sum.vanishing hU
  simp only [mem_setOf_eq] at hs_tail
  have hP_g : ∏' k, (1 + g k) = (∏ k ∈ s, (1 + g k)) * ∏' k : {k // k ∉ s}, (1 + g k) :=
    ((s.hasProd (fun k ↦ 1 + g k)).mul_compl (multipliable_one_add_of_summable
    (hsum_g.comp_injective Subtype.val_injective)).hasProd).tprod_eq
  have hBP_f : ∀ᶠ n in 𝓕, ‖(∏' k : {k // k ∉ s}, (1 + f n k)) - 1‖ ≤ δ ∧
      ∏' k, (1 + f n k) = (∏ k ∈ s, (1 + f n k)) * ∏' k : {k // k ∉ s}, (1 + f n k) := by
    filter_upwards [h_bound] with n hn
    have hmn_compl : Multipliable (fun k : {k // k ∉ s} ↦ 1 + f n k) :=
      multipliable_one_add_of_summable
      (( h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hn).comp_injective Subtype.val_injective)
    exact ⟨norm_tprod_tail_sub_one_le h_sum hn hs_tail,
      ((s.hasProd (fun k ↦ 1 + f n k)).mul_compl hmn_compl.hasProd).tprod_eq⟩
  have h4Cδ : 4 * C * δ ≤ ε := by
    calc 4 * C * δ ≤ 4 * C * (ε / (4 * C)) := by gcongr; exact min_le_right _ _
      _ = ε := by field_simp
  have HH : ∀ᶠ (n : α) in 𝓕, dist (∏' (k : β), (1 + f n k)) (∏' (k : β), (1 + g k)) < 4 * rexp
      (∑' (k : β), bound k) * δ := by
    have hε4 : (0 : ℝ) < 4 * rexp (∑' (k : β), bound k) * δ  / 4 := by positivity
    have hA_norm : ‖∏ k ∈ s, (1 + g k)‖ ≤ C := norm_head_prod_le_exp_tsum s h_bound_g h_sum
    filter_upwards [h_bound, (hBP_f.mono fun _ h ↦ h.1), (hBP_f.mono fun _ h ↦ h.2),
      (tendsto_finset_prod s (fun k _ ↦ (hab k).const_add 1)).eventually (ball_mem_nhds _ hε4)]
      with n hn hPn hBn_close hAn_close
    rw [dist_eq_norm, hP_g, hBn_close]
    exact tendsto_tprod_final_estimate_aux hPn (norm_tprod_tail_sub_one_le h_sum h_bound_g hs_tail)
      hAn_close (min_le_left _ _) hA_norm hC_pos rfl
  exact HH.mono (fun n hn ↦ hn.trans_le h4Cδ)

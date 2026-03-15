/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable
public import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Infinite products in normed rings

This file proves a dominated convergence theorem for infinite products of terms of the form
`(1 + f n k)` in a complete normed commutative ring, by reducing to the additive version
(Tannery's theorem) via the formal expansion `∏ (1 + f i) = ∑ₛ ∏ᵢ∈ₛ f i`.

## Main results

* `tendsto_tprod_one_add_of_dominated_convergence`: if `f n k → g k` pointwise and
  `‖f n k‖ ≤ bound k` eventually with `bound` summable, then
  `∏' k, (1 + f n k) → ∏' k, (1 + g k)`.
-/

open Topology Filter Metric Real Set

variable {α R β : Type*} [NormedCommRing R] [NormOneClass R] [CompleteSpace R] {g : β → R}
  {bound : β → ℝ}

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
  have hsum_g : Summable (‖g ·‖) := h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) h_bound_g
  rw [show ∏' k, (1 + g k) = ∑' s : Finset β, ∏ i ∈ s, g i from
    tprod_one_add (α := R) (summable_finset_prod_of_summable_norm hsum_g)]
  exact (tendsto_tsum_of_dominated_convergence (G := R) (f := fun n (s : Finset β) ↦ ∏ i ∈ s, f n i)
    (bound := fun (s : Finset β) ↦ ∏ i ∈ s, bound i) (summable_finset_prod_of_summable_nonneg
    (fun i ↦ (norm_nonneg (g i)).trans (h_bound_g i)) h_sum)
    (fun s ↦ tendsto_finset_prod s fun i _ ↦ hab i)
    (h_bound.mono fun n hn (s : Finset β) ↦ (Finset.norm_prod_le s (f n)).trans
    (Finset.prod_le_prod (fun i _ ↦ norm_nonneg _) fun i _ ↦ hn i))).congr'
    (h_bound.mono fun n hn ↦ (tprod_one_add (α := R) (summable_finset_prod_of_summable_norm
    (h_sum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hn))).symm)

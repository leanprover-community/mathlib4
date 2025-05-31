/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
import Mathlib.Analysis.SpecialFunctions.Pochhammer
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Combinatorics.SimpleGraph.Bipartite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic

/-!
# The Kővári–Sós–Turán theorem

This file proves the **Kővári–Sós–Turán theorem** for simple graphs.

## Main definitions

* `SimpleGraph.card_edgeFinset_le_of_completeBipartiteGraph_free` is the proof of the
  **Kővári–Sós–Turán theorem** for simple graphs:

  The `(completeBipartiteGraph α β).Free` simple graphs for `card α ≤ card β` on the vertex type `V`
  have at most `(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2 + (card V)*(card α-1)/2` edges.

* `SimpleGraph.extremalNumber_completeBipartiteGraph_le` is the corollary of the
  **Kővári–Sós–Turán theorem** upper bounding the extremal numbers of `completeBipartiteGraph α β`.
-/


open Finset Fintype

namespace SimpleGraph

variable {V α β : Type*} [Fintype V] [Fintype α] [Fintype β]

namespace KovariSosTuran

/-- `bound` is the upper bound in the statement of the **Kővári–Sós–Turán theorem**.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
noncomputable abbrev bound (n s t : ℕ) : ℝ :=
  (t-1)^(1/s : ℝ)*n^(2-1/s : ℝ)/2 + n*(s-1)/2

theorem bound_nonneg {n s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) : 0 ≤ bound n s t := by
    apply add_nonneg <;> apply div_nonneg _ zero_le_two <;> apply mul_nonneg
    · apply Real.rpow_nonneg <| sub_nonneg_of_le (mod_cast hs.trans ht)
    · apply Real.rpow_nonneg n.cast_nonneg
    · exact n.cast_nonneg
    · exact sub_nonneg_of_le (mod_cast hs)

variable [DecidableEq V]

/-- `aux` is the set of pairs `(t, v)` such that `t : Finset V` is an `n`-sized subset of the
neighbor finset of `v : V` in `G : SimpleGraph V`.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private abbrev aux (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) :=
  (univ.powersetCard n ×ˢ univ).filter fun (t, v) ↦ t ⊆ G.neighborFinset v

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local notation "X" => aux G (card α)

/-- If `G` is `(completeBipartiteGraph α β).Free`, then `#X` is at most the number
of ways to choose `card α` vertices from `card V` vertices `card β-1` times.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private lemma card_aux_le [Nonempty β] (h : (completeBipartiteGraph α β).Free G) :
    #X ≤ (((card V).choose (card α))*(card β-1) : ℝ) := by
  simp_rw [card_filter _, sum_product, ← card_filter, ← @card_univ V, ← card_powersetCard,
    ← nsmul_eq_mul, ← sum_const, ← Nat.cast_pred card_pos, ← Nat.cast_sum, Nat.cast_le]
  apply sum_le_sum
  intro t ht_mem
  contrapose! h
  rw [not_free, completeBipartiteGraph_isContained_iff]
  have ⟨t', ht'_sub⟩ := exists_subset_card_eq h
  rw [← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos card_pos] at ht'_sub
  have ht'_mem : t' ∈ univ.powersetCard (Fintype.card β) := by
    simpa [mem_powersetCard_univ] using ht'_sub.2
  use ⟨t, ht_mem⟩, ⟨t', ht'_mem⟩
  intro v₁ hv₁ v₂ hv₂
  replace hv₂ := ht'_sub.1 hv₂
  rw [mem_filter] at hv₂
  replace hv₁ := hv₂.2 hv₁
  rw [mem_neighborFinset] at hv₁
  exact hv₁.symm

/-- If the average degree of vertices in `G` is at least `card α-1`, then it follows from a special
case of Jensen's inequality for `Nat.choose` that `#X` is at least `card α` times
the desending pochhammer function evaluated at the average divided by `(card α).factorial`.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private lemma le_card_aux [Nonempty V] [Nonempty α]
    (h_avg : card α-1 ≤ (∑ v : V, G.degree v : ℝ)/card V) :
    ((card V)*((descPochhammer ℝ (card α)).eval
        ((∑ v, G.degree v : ℝ)/card V)/(card α).factorial) : ℝ) ≤ #X := by
  simp_rw [card_filter _, sum_product_right, ← card_filter, powersetCard_eq_filter,
    filter_comm, powerset_univ, filter_subset_univ, ← powersetCard_eq_filter,
    card_powersetCard, card_neighborFinset_eq_degree, Nat.cast_sum,
    ← le_inv_mul_iff₀ (mod_cast card_pos : 0 < (card V : ℝ)), mul_sum,
    div_eq_mul_inv _ (card V : ℝ), mul_comm _ (card V : ℝ)⁻¹, mul_sum]
  apply descPochhammer_eval_div_factorial_le_sum_choose (by positivity) _ _ (by simp) (by simp)
  rwa [div_eq_inv_mul, mul_sum] at h_avg

/-- If the average degree of vertices in `G` is at least `card α-1` and `G` is
`(completeBipartiteGraph α β).Free`, then `G` has at most `KovariSosTuran.bound` edges.

This is an auxiliary definition for the **Kővári–Sós–Turán theorem**. -/
private lemma card_edgeFinset_le_bound [Nonempty V] [Nonempty α] [Nonempty β]
    (h_avg : card α-1 ≤ (∑ v : V, G.degree v : ℝ) / card V)
    (h_free : (completeBipartiteGraph α β).Free G) :
    #G.edgeFinset ≤ bound (card V) (card α) (card β) := by
  have h_avg_sub_nonneg : 0 ≤ (2*#G.edgeFinset/card V-card α+1 : ℝ) := by
    rwa [← Nat.cast_sum, sum_degrees_eq_twice_card_edges, Nat.cast_mul,
      Nat.cast_two, ← sub_nonneg, ← sub_add] at h_avg
  suffices h : ((card V)*(2*#G.edgeFinset/card V-card α+1)^(card α)/(card α).factorial : ℝ)
      ≤ (((card V)^(card α)/(card α).factorial)*(card β-1) : ℝ) by
    rwa [mul_comm _ (card β-1 : ℝ), mul_div, div_le_div_iff_of_pos_right,
      mul_comm (card β-1 : ℝ) _, ← Real.rpow_natCast, ← Real.rpow_natCast,
      mul_comm _ ((card β)-1 : ℝ), ← Real.rpow_le_rpow_iff, Real.mul_rpow, Real.mul_rpow,
      Real.rpow_rpow_inv, Real.rpow_rpow_inv, sub_add, mul_sub, sub_le_iff_le_add, mul_div,
      div_le_iff₀, ← mul_assoc, ← le_div_iff₀', add_mul, add_div, ← div_div,
      div_eq_mul_inv _ (_^(card α : ℝ)⁻¹: ℝ), ← Real.rpow_neg_one (_^(card α : ℝ)⁻¹ : ℝ),
      ← Real.rpow_mul, mul_neg_one, mul_assoc, mul_comm (card V : ℝ) _, ← Real.rpow_add_one,
      mul_assoc, mul_comm (card V : ℝ) _, ← Real.rpow_add_one, add_assoc, one_add_one_eq_two,
      add_comm _ 2, ← sub_eq_add_neg, ← div_div, div_eq_mul_inv _ (_^(card α : ℝ)⁻¹ : ℝ),
      ← Real.rpow_neg_one (_^(card α : ℝ)⁻¹ : ℝ), ← Real.rpow_mul, mul_neg_one, mul_assoc,
      mul_comm (card V : ℝ) _, ← Real.rpow_add_one, mul_assoc, mul_comm (card α-1 : ℝ) _,
      ← mul_assoc, ← Real.rpow_add, ← add_assoc, add_neg_cancel, zero_add, Real.rpow_one,
      inv_eq_one_div] at h
    any_goals apply mul_nonneg
    any_goals
      apply sub_nonneg_of_le
      rw [Nat.one_le_cast]
      apply Nat.succ_le_of_lt
    any_goals positivity
  -- double-counting `(t, v) ↦ t ⊆ G.neighborSet v`
  trans (#X : ℝ)
  -- counting `t`
  · trans (card V)*((descPochhammer ℝ (card α)).eval
        ((∑ v, G.degree v : ℝ)/card V)/(card α).factorial)
    · rw [← Nat.cast_two, ← Nat.cast_mul, ← sum_degrees_eq_twice_card_edges, Nat.cast_sum,
        mul_div, div_le_div_iff_of_pos_right (by positivity), mul_le_mul_left (by positivity)]
      exact pow_le_descPochhammer_eval h_avg
    · exact le_card_aux h_avg
  -- counting `v`
  · trans ((card V).choose (card α))*(card β-1)
    · exact card_aux_le h_free
    · apply mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div (card α) (card V))
      exact sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)

end KovariSosTuran

variable [DecidableEq V]

/-- The `(completeBipartiteGraph α β).Free` simple graphs on the vertex type `V` have at most
`(card β-1)^(1/(card α))*(card V)^(2-1/(card α))/2 + (card V)*(card α-1)/2` edges.

This is the **Kővári–Sós–Turán theorem**. -/
theorem card_edgeFinset_le_of_completeBipartiteGraph_free
    [Nonempty α] (hcard_le : card α ≤ card β) {G : SimpleGraph V} [DecidableRel G.Adj]
    (h_free : (completeBipartiteGraph α β).Free G) :
    #G.edgeFinset
      ≤ ((card β-1)^(1/card α : ℝ)*(card V)^(2-1/card α : ℝ)/2 + (card V)*(card α-1)/2 : ℝ) := by
  haveI : Nonempty β := by
    rw [← card_pos_iff]
    exact card_pos.trans_le hcard_le
  cases isEmpty_or_nonempty V
  · have h_two_sub_one_div_ne_zero : 2 - (card α : ℝ)⁻¹ ≠ 0 := by
      apply sub_ne_zero_of_ne ∘ ne_of_gt
      exact (card α).cast_inv_le_one.trans_lt one_lt_two
    simp [h_two_sub_one_div_ne_zero]
  · rcases lt_or_le (∑ v, G.degree v : ℝ) ((card V)*(card α-1) : ℝ) with h_sum_lt | h_avg
    -- if avg degree less than `card a-1`
    · rw [← Nat.cast_sum, sum_degrees_eq_twice_card_edges,
        Nat.cast_mul, Nat.cast_two, ← lt_div_iff₀' zero_lt_two] at h_sum_lt
      apply h_sum_lt.le.trans
      apply le_add_of_nonneg_left
      apply div_nonneg _ zero_le_two
      apply mul_nonneg
      · apply Real.rpow_nonneg _ (1/card α)
        exact sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)
      · exact Real.rpow_nonneg (card V).cast_nonneg (2-1/card α)
    -- -- if avg degree at least `card α-1`
    · rw [← le_div_iff₀' (mod_cast card_pos)] at h_avg
      exact KovariSosTuran.card_edgeFinset_le_bound h_avg h_free

/-- The extremal numbers of `completeBipartiteGraph α β` are at most
`(card β-1)^(1/card α)*n^(2-1/card α)/2 + n*(card α-1)/2`.

This is the corollary of the **Kővári–Sós–Turán theorem** for extremal numbers. -/
theorem extremalNumber_completeBipartiteGraph_le (n : ℕ) [Nonempty α] (hcard_le : card α ≤ card β) :
  extremalNumber n (completeBipartiteGraph α β)
    ≤ ((card β-1)^(1/card α : ℝ)*n^(2-1/card α : ℝ)/2 + n*(card α-1)/2 : ℝ) := by
  rw [← Fintype.card_fin n,
    extremalNumber_le_iff_of_nonneg _ <| KovariSosTuran.bound_nonneg card_pos hcard_le]
  intro G _ h_free
  exact card_edgeFinset_le_of_completeBipartiteGraph_free hcard_le h_free

end SimpleGraph

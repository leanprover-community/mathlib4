/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz

/-!
# The Kővári-Sós-Turán theorem

This file proves the **Kővári-Sós-Turán theorem** for the Zarankiewicz function and simple graphs.

## Main definitions

* `SimpleGraph.zarankiewicz_le` is the **Kővári-Sós-Turán theorem** upper bounding the
  zarankiewicz function.

* `SimpleGraph.extremalNumber_completeBipartiteGraph_le` is the corollary of the
  **Kővári-Sós-Turán theorem** upper bounding the extremal numbers of `completeBipartiteGraph α β`.
-/

@[expose] public section


open Finset Fintype

namespace SimpleGraph

variable {V W α β : Type*} [Fintype V] [Fintype W] [Fintype α] [Fintype β]

namespace KovariSosTuran

/-- `KovariSosTuran.bound` is the upper bound in the statement of the **Kővári-Sós-Turán theorem**.

This is an auxiliary definition for the **Kővári-Sós-Turán theorem**. -/
noncomputable abbrev bound (m n s t : ℕ) : ℝ :=
  (t - 1) ^ (s⁻¹ : ℝ) * m * n ^ (1 - (s⁻¹ : ℝ)) + (s - 1) * n

theorem bound_nonneg (m n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 ≤ bound m n s t := by
  apply add_nonneg <;> repeat apply mul_nonneg
  · exact Real.rpow_nonneg (sub_nonneg_of_le (mod_cast ht)) (s : ℝ)⁻¹
  · exact m.cast_nonneg
  · exact Real.rpow_nonneg n.cast_nonneg (1 - (s : ℝ)⁻¹)
  · exact sub_nonneg_of_le (mod_cast hs)
  · exact n.cast_nonneg

/-- `KovariSosTuran.filter` is the finset of pairs `(t, w)` such that `t : Finset V` is an
`n`-sized subset of the neighbor finset of `w : W` in `G : SimpleGraph V ⊕ W`.

This is an auxiliary definition for the **Kővári-Sós-Turán theorem**. -/
abbrev filter [DecidableEq V] [DecidableEq W]
  (G : SimpleGraph (V ⊕ W)) [DecidableRel G.Adj] (n : ℕ) :=
  ((univ.map .inl).powersetCard n ×ˢ (univ.map .inr)).filter fun (t, w) ↦ t ⊆ G.neighborFinset w

variable {G : SimpleGraph (V ⊕ W)} [DecidableRel G.Adj]

open Classical in
/-- If `G` is `(completeBipartiteGraph α β).Free`, then `#KovariSosTuran.filter` is at most the
number of ways to choose `card α` vertices from `card V` vertices `card β - 1` times.

This is an auxiliary lemma for the **Kővári-Sós-Turán theorem**. -/
lemma card_filter_le [Nonempty β] (h : (completeBipartiteGraph α β).Free G) :
    #(filter G (card α)) ≤ ((card V).choose (card α) * (card β - 1) : ℝ) := by
  have hcard_univ_map_inl : #(univ.map .inl : Finset (V ⊕ W)) = card V := by
    rw [card_map, card_univ]
  simp_rw [card_filter, sum_product, ← card_filter, ← hcard_univ_map_inl, ← card_powersetCard,
    ← nsmul_eq_mul, ← sum_const, ← Nat.cast_pred card_pos, ← Nat.cast_sum, Nat.cast_le]
  refine sum_le_sum (fun t ht_card ↦ ?_)
  contrapose! h
  obtain ⟨_, ht_card⟩ := mem_powersetCard.mp ht_card
  have ⟨t', ht'_sub, ht'_card⟩ := exists_subset_card_eq h
  rw [← Nat.pred_eq_sub_one, Nat.succ_pred_eq_of_pos card_pos] at ht'_card
  rw [completeBipartiteGraph_isContained_iff]
  refine ⟨t, t', ht_card, ht'_card, fun v hv w hw ↦ ?_⟩
  apply ht'_sub at hw
  rw [mem_filter] at hw
  apply hw.2 at hv
  rw [mem_neighborFinset] at hv
  exact hv.symm

open Classical in
/-- If the average degree of vertices in the left part of `G : SimpleGraph V ⊕ W` is at
least `card α - 1`, then it follows from a special case of *Jensen's inequality* for `Nat.choose`
that `#KovariSosTuran.filter` is at least `card α` times the desending pochhammer function
evaluated at the average divided by `(card α).factorial`.

This is an auxiliary lemma for the **Kővári-Sós-Turán theorem**. -/
lemma le_card_filter [Nonempty W] [Nonempty α]
    (h_le : G ≤ completeBipartiteGraph V W)
    (h_avg : card α - 1 ≤ (∑ w : W, G.degree (.inr w) : ℝ) / card W) :
    (card W * ((descPochhammer ℝ (card α)).eval
        ((∑ w : W, G.degree (.inr w) : ℝ) / card W) / (card α).factorial) : ℝ)
      ≤ #(filter G (card α)) := by
  have h_subset (x) (hx : x ∈ univ.map .inr) :
      (G.neighborFinset x).powerset ⊆ (map Function.Embedding.inl univ).powerset := by
    simp_rw [powerset_mono, neighborFinset_eq_filter, subset_iff, mem_filter, mem_univ,
      mem_map, mem_univ, true_and, Function.Embedding.inl_apply, eq_comm, ← Sum.isLeft_iff]
    intro y hadj
    simp_rw [mem_map, mem_univ, Function.Embedding.inr_apply,
      true_and, eq_comm, ← Sum.isRight_iff] at hx
    simpa [hx, Sum.not_isLeft.mpr hx] using h_le hadj
  have h_card_filter_subset_eq (x) (hx : x ∈ univ.map .inr) :
      #{x ∈ (univ.map .inl).powerset ∩ (G.neighborFinset x).powerset | #x = card α}
        = #{x ∈ (G.neighborFinset x).powerset | #x = card α} := by
    simp_rw [inter_eq_right.mpr <| h_subset x hx]
  simp_rw [card_filter, sum_product_right, ← card_filter, powersetCard_eq_filter,
    filter_comm, ← mem_powerset, filter_mem_eq_inter, sum_congr rfl h_card_filter_subset_eq,
    ← powersetCard_eq_filter, card_powersetCard, card_neighborFinset_eq_degree, Nat.cast_sum,
    ← le_inv_mul_iff₀ (mod_cast card_pos : 0 < (card W : ℝ)), mul_sum,
    div_eq_mul_inv _ (card W : ℝ), mul_comm _ (card W : ℝ)⁻¹, mul_sum, sum_map,
    Function.Embedding.inr_apply]
  rw [div_eq_inv_mul, mul_sum] at h_avg
  exact descPochhammer_eval_div_factorial_le_sum_choose
    (by positivity) _ _ (by simp) (by simp) h_avg

open Classical in
/-- An upper bound on the number of edges in `completeBipartiteGraph α β`-free bipartite graphs.

This is an auxiliary lemma for the **Kővári-Sós-Turán theorem**. -/
lemma card_edgeFinset_le_bound_of_completeBipartiteGraph_free [Nonempty α] [Nonempty β]
    (h_le : G ≤ completeBipartiteGraph V W) (h_free : (completeBipartiteGraph α β).Free G) :
    #G.edgeFinset ≤ bound (card V) (card W) (card α) (card β) := by
  cases isEmpty_or_nonempty W
  · have h_bot : completeBipartiteGraph V W = ⊥ := by
      simp_rw [SimpleGraph.ext_iff, funext_iff, eq_iff_iff, completeBipartiteGraph_adj,
      ← Sum.isRight_eq_false, bot_adj, iff_false, not_or, not_and_or, Bool.not_eq_false,
      Sum.isRight_iff, IsEmpty.exists_iff, not_false_eq_true, true_or, and_true, or_true,
      implies_true]
    rw [h_bot, le_bot_iff] at h_le
    simp_rw [Set.toFinset_card, h_le, edgeSet_bot, ← Set.toFinset_card,
      Set.toFinset_empty, Finset.card_empty, Nat.cast_zero]
    exact bound_nonneg (card V) (card W)
      (Nat.one_le_cast.mpr card_pos) (Nat.one_le_cast.mpr card_pos)
  · have h_isBipartiteWith : G.IsBipartiteWith
        (univ.map .inl : Finset (V ⊕ W)) (univ.map .inr : Finset (V ⊕ W)) := by
      refine ⟨?_, fun v w hadj ↦ ?_⟩
      · simp [Set.disjoint_iff_forall_ne]
      · simp_rw [coe_map, Function.Embedding.inl_apply, Function.Embedding.inr_apply,
          coe_univ, Set.image_univ, Set.mem_range, eq_comm, ← Sum.isLeft_iff, ← Sum.isRight_iff]
        exact h_le hadj
    have h_sum_degrees_eq_card_edges : ∑ w : W, ↑(G.degree (Sum.inr w)) = #G.edgeFinset := by
      simp_rw [← isBipartiteWith_sum_degrees_eq_card_edges' h_isBipartiteWith,
        Finset.sum_map, Function.Embedding.inr_apply]
    rcases lt_or_ge (∑ w : W, G.degree (.inr w) : ℝ) ((card α - 1) * (card W) : ℝ)
        with h_sum_lt | h_avg
    -- if avg degree less than `card a - 1`
    · simp_rw [← Nat.cast_sum, h_sum_degrees_eq_card_edges] at h_sum_lt
      apply h_sum_lt.le.trans
      apply le_add_of_nonneg_left
      repeat apply mul_nonneg
      · exact Real.rpow_nonneg (sub_nonneg_of_le <| Nat.one_le_cast.mpr card_pos) _
      · exact (card V).cast_nonneg
      · exact Real.rpow_nonneg (card W).cast_nonneg _
    -- -- if avg degree at least `card α - 1`
    · rw [← le_div_iff₀ (mod_cast card_pos)] at h_avg
      suffices h : card W * (#G.edgeFinset / card W - card α + 1) ^ card α / (card α).factorial
          ≤ ((card V ^ card α / (card α).factorial) * (card β - 1) : ℝ) by
        have hcard_sub_one_nonneg : 0 ≤ (card β - 1 : ℝ) :=
          sub_nonneg_of_le (Nat.one_le_cast.mpr card_pos)
        have h_avg' : 0 ≤ (#G.edgeFinset / card W - card α + 1 : ℝ) := by
          rwa [← Nat.cast_sum, h_sum_degrees_eq_card_edges, ← sub_nonneg, ← sub_add] at h_avg
        -- rearrange expression for `bound`
        rwa [mul_comm _ (card β - 1 : ℝ), mul_div, div_le_div_iff_of_pos_right (by positivity),
          ← Real.rpow_le_rpow_iff (by positivity) (by positivity)
            (by positivity : 0 < (card α : ℝ)⁻¹), Real.mul_rpow (by positivity) (by positivity),
          Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
          ← Real.rpow_natCast, Real.rpow_rpow_inv (by positivity) (by positivity),
          Real.rpow_rpow_inv (by positivity) (by positivity), sub_add, mul_sub, sub_le_iff_le_add,
          mul_div, div_le_iff₀ (by positivity), ← le_div_iff₀' (by positivity), add_mul, add_div,
          div_eq_mul_inv _ (_ ^ (card α : ℝ)⁻¹: ℝ), ← Real.rpow_neg_one (_ ^ (card α : ℝ)⁻¹ : ℝ),
          ← Real.rpow_mul (by positivity), mul_neg_one, mul_assoc, mul_comm (card W : ℝ) _,
          ← Real.rpow_add_one (by positivity), neg_add_eq_sub,
          div_eq_mul_inv _ (_ ^ (card α : ℝ)⁻¹ : ℝ), ← Real.rpow_neg_one (_ ^ (card α : ℝ)⁻¹ : ℝ),
          ← Real.rpow_mul (by positivity), mul_neg_one, mul_rotate _ (card α - 1 : ℝ),
          mul_assoc (card α - 1 : ℝ), mul_assoc (card α - 1 : ℝ), mul_assoc (card W : ℝ),
          ← Real.rpow_add (by positivity), add_neg_cancel, Real.rpow_zero, mul_one] at h
      -- double-counting `(t, v) ↦ t ⊆ G.neighborSet v`
      trans (#(filter G (card α)) : ℝ)
      -- counting `t`
      · trans (card W) * ((descPochhammer ℝ (card α)).eval
          ((∑ w : W, G.degree (.inr w) : ℝ) / card W) / (card α).factorial)
        · rw [← h_sum_degrees_eq_card_edges, Nat.cast_sum, mul_div,
            div_le_div_iff_of_pos_right (by positivity), mul_le_mul_iff_right₀ (by positivity)]
          exact pow_le_descPochhammer_eval h_avg
        · exact le_card_filter h_le h_avg
      -- counting `v`
      · trans (card V).choose (card α) * (card β - 1)
        · exact card_filter_le h_free
        · exact mul_le_mul_of_nonneg_right (mod_cast Nat.choose_le_pow_div (card α) (card V)) <|
            sub_nonneg_of_le (mod_cast Nat.succ_le_of_lt card_pos)

end KovariSosTuran

/-- An upper bound on the Zarankiewicz function.

This is the **Kővári-Sós-Turán theorem**. -/
theorem zarankiewicz_le (m n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) :
    zarankiewicz m n s t
      ≤ ((t - 1) ^ (s⁻¹ : ℝ) * m * n ^ (1 - (s⁻¹ : ℝ)) + (s - 1) * n : ℝ) := by
  have hs' : 1 ≤ card (Fin s) := by rwa [← Fintype.card_fin s] at hs
  have ht' : card (Fin s) ≤ card (Fin t) := by
    rwa [← Fintype.card_fin s, ← Fintype.card_fin t] at ht
  rw [← Fintype.card_fin m, ← Fintype.card_fin n, ← Fintype.card_fin s, ← Fintype.card_fin t,
    ← KovariSosTuran.bound, zarankiewicz_le_iff_of_nonneg <|
    KovariSosTuran.bound_nonneg _ _ hs' (hs'.trans ht')]
  intro G _
  have : NeZero s := ⟨Nat.pos_iff_ne_zero.mp hs⟩
  have : NeZero t := ⟨Nat.pos_iff_ne_zero.mp <| hs.trans ht⟩
  exact KovariSosTuran.card_edgeFinset_le_bound_of_completeBipartiteGraph_free

/-- An upper bound on the symmetric Zarankiewicz function.

This is a corollary of the **Kővári-Sós-Turán theorem**. -/
theorem symm_zarankiewicz_le (n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) :
    zarankiewicz n n s t
      ≤ ((t - 1) ^ (s : ℝ)⁻¹ * n ^ (2 - (s : ℝ)⁻¹) + (s - 1) * n : ℝ) := by
  have hone_add_one_sub_inv_card_ne_zero : 1 + (1 - (s : ℝ)⁻¹) ≠ 0 := by
      rw [← add_sub_assoc, ← show (2 : ℝ) = (1 : ℝ) + (1 : ℝ) by norm_num]
      exact sub_ne_zero_of_ne <| ne_of_gt <| s.cast_inv_le_one.trans_lt one_lt_two
  rw [show (2 : ℝ) = (1 : ℝ) + (1 : ℝ) by norm_num, add_sub_assoc,
    Real.rpow_one_add' (by positivity) hone_add_one_sub_inv_card_ne_zero, ← mul_assoc]
  exact zarankiewicz_le n n hs ht

/-- An upper bound on the extremal numbers of `completeBipartiteGraph α β`.

This is a corollary of the **Kővári-Sós-Turán theorem**. -/
theorem extremalNumber_completeBipartiteGraph_le
    (n : ℕ) [Nonempty α] (hcard_le : card α ≤ card β) :
    (extremalNumber n (completeBipartiteGraph α β) : ℝ)
      ≤ (card β - 1) ^ (card α : ℝ)⁻¹ * n ^ (2 - (card α : ℝ)⁻¹) / 2 + (card α - 1) * n / 2 := by
  have : Nonempty β := card_pos_iff.mp <|  card_pos.trans_le hcard_le
  rw [← add_div, le_div_iff₀' zero_lt_two, ← Nat.cast_two, ← Nat.cast_mul]
  exact (symm_zarankiewicz_le n card_pos hcard_le).trans' <|
    mod_cast two_mul_extremalNumber_le_zarankiewicz_symm

end SimpleGraph

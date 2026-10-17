/-
Copyright (c) 2026 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pochhammer
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Zarankiewicz

/-!
# The Kővári-Sós-Turán theorem

This file proves the **Kővári-Sós-Turán theorem** for the Zarankiewicz function and simple graphs.

## Main definitions

* `SimpleGraph.zarankiewicz_le` is the **Kővári-Sós-Turán theorem** upper bounding the
  Zarankiewicz function.

* `SimpleGraph.extremalNumber_completeBipartiteGraph_le` is the corollary of the
  **Kővári-Sós-Turán theorem** upper bounding the extremal numbers of `completeBipartiteGraph α β`.
-/

open Finset Fintype

namespace SimpleGraph

variable {V W α β : Type*} [Fintype V] [Fintype W] [Fintype α] [Fintype β]

namespace KovariSosTuran

/-- `KovariSosTuran.bound` is the upper bound in the statement of the **Kővári-Sós-Turán theorem**.

This is an auxiliary definition for the **Kővári-Sós-Turán theorem**. -/
noncomputable abbrev bound (m n s t : ℕ) : ℝ :=
  (t - 1) ^ (s⁻¹ : ℝ) * m * n ^ (1 - (s⁻¹ : ℝ)) + (s - 1) * n

theorem bound_nonneg (m n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : 1 ≤ t) : 0 ≤ bound m n s t := by
  positivity [(mod_cast hs : (1 : ℝ) ≤ s), (mod_cast ht : (1 : ℝ) ≤ t)]

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
  simp_rw [card_filter, sum_product, ← card_filter, ← card_univ (α := V),
    ← card_map (.inl : V ↪ V ⊕ W), ← card_powersetCard, ← nsmul_eq_mul, ← sum_const,
    ← Nat.cast_pred card_pos, ← Nat.cast_sum, Nat.cast_le]
  refine sum_le_sum fun t ht_card ↦ ?_
  contrapose! h
  obtain ⟨_, ht_card⟩ := mem_powersetCard.mp ht_card
  obtain ⟨t', ht'_sub, ht'_card⟩ := exists_subset_card_eq (Nat.le_of_pred_lt h)
  exact completeBipartiteGraph_isContained_iff.mpr ⟨t, t', ht_card, ht'_card,
    fun v hv w hw ↦ ((mem_neighborFinset ..).mp <| (mem_filter.mp <| ht'_sub hw).right hv).symm⟩

open Classical in
/-- If the average degree of vertices in the left part of `G : SimpleGraph V ⊕ W` is at
least `card α - 1`, then it follows from a special case of *Jensen's inequality* for `Nat.choose`
that `#KovariSosTuran.filter` is at least `card α` times the descending Pochhammer function
evaluated at the average divided by `(card α).factorial`.

This is an auxiliary lemma for the **Kővári-Sós-Turán theorem**. -/
lemma le_card_filter [Nonempty W] [Nonempty α]
    (h_le : G ≤ completeBipartiteGraph V W)
    (h_avg : card α - 1 ≤ (∑ w : W, G.degree (.inr w) : ℝ) / card W) :
    (card W * ((descPochhammer ℝ (card α)).eval
        ((∑ w : W, G.degree (.inr w) : ℝ) / card W) / (card α).factorial) : ℝ)
      ≤ #(filter G (card α)) := by
  -- neighborhoods of right vertices lie in the left part
  have h_nbhd (w : W) : G.neighborFinset (.inr w) ⊆ univ.map .inl := fun v hv ↦ by
    replace hv : v.isLeft := by simpa using h_le <| (mem_neighborFinset ..).mp hv
    simp [eq_comm, Sum.isLeft_iff.mp hv]
  -- `KovariSosTuran.filter` counts the `card α`-subsets of the neighborhoods
  have hcard_filter : #(filter G (card α)) = ∑ w : W, (G.degree (.inr w)).choose (card α) := by
    simp_rw [card_filter, sum_product_right, ← card_filter, sum_map,
      ← card_neighborFinset_eq_degree, ← card_powersetCard]
    refine sum_congr rfl fun w _ ↦ congrArg card <| Finset.ext fun _ ↦ ?_
    rw [mem_filter, mem_powersetCard, mem_powersetCard]
    exact ⟨fun ⟨⟨_, hcard⟩, hsubet⟩ ↦ ⟨hsubet, hcard⟩,
      fun ⟨hsubset, hcard⟩ ↦ ⟨⟨hsubset.trans (h_nbhd w), hcard⟩, hsubset⟩⟩
  rw [div_eq_inv_mul, mul_sum] at h_avg
  have h_jensen := descPochhammer_eval_div_factorial_le_sum_choose
    (by positivity) (fun w : W ↦ G.degree (.inr w)) _ (fun _ _ ↦ by positivity) (by simp) h_avg
  rw [← mul_sum, ← div_eq_inv_mul] at h_jensen
  rw [hcard_filter, Nat.cast_sum]
  apply (mul_le_mul_of_nonneg_left h_jensen (by positivity)).trans_eq
  rw [← mul_sum, mul_inv_cancel_left₀ <| Nat.cast_ne_zero.mpr card_pos.ne']

/-- An upper bound on the number of edges in `completeBipartiteGraph α β`-free bipartite graphs.

This is an auxiliary lemma for the **Kővári-Sós-Turán theorem**. -/
lemma card_edgeFinset_le_bound_of_completeBipartiteGraph_free [Nonempty α] [Nonempty β]
    (h_le : G ≤ completeBipartiteGraph V W) (h_free : (completeBipartiteGraph α β).Free G) :
    #G.edgeFinset ≤ bound (card V) (card W) (card α) (card β) := by
  cases isEmpty_or_nonempty W
  · rw [Finset.card_eq_zero.mpr <| edgeFinset_eq_empty.mpr <| le_bot_iff.mp <|
      h_le.trans_eq completeBipartiteGraph_eq_bot_of_isEmpty_right, Nat.cast_zero]
    exact bound_nonneg (card V) (card W)
      (Nat.one_le_cast.mpr card_pos) (Nat.one_le_cast.mpr card_pos)
  · have h_isBipartiteWith : G.IsBipartiteWith
        (univ.map .inl : Finset (V ⊕ W)) (univ.map .inr : Finset (V ⊕ W)) := by
      simpa using (IsBipartiteWith.completeBipartiteGraph V W).anti h_le
    have h_sum_degrees_eq_card_edges : ∑ w : W, ↑(G.degree (Sum.inr w)) = #G.edgeFinset := by
      rw [← isBipartiteWith_sum_degrees_eq_card_edges' h_isBipartiteWith, sum_map]
      rfl
    rcases lt_or_ge (∑ w : W, G.degree (.inr w) : ℝ) ((card α - 1) * (card W) : ℝ)
        with h_sum_lt | h_avg
    -- if avg degree less than `card a - 1`
    · simp_rw [← Nat.cast_sum, h_sum_degrees_eq_card_edges] at h_sum_lt
      refine h_sum_lt.le.trans <| le_add_of_nonneg_left ?_
      positivity [(mod_cast card_pos : (1 : ℝ) ≤ Fintype.card β)]
    -- if avg degree at least `card α - 1`
    · rw [← le_div_iff₀ (mod_cast card_pos)] at h_avg
      -- double-counting `(t, v) ↦ t ⊆ G.neighborSet v`
      have h : (card W * (#G.edgeFinset / card W - card α + 1) ^ card α / (card α).factorial : ℝ) ≤
          (card V ^ card α / (card α).factorial) * (card β - 1) := by
        classical
        trans (#(filter G (card α)) : ℝ)
        -- counting `t`
        · trans (card W) * ((descPochhammer ℝ (card α)).eval
            ((∑ w : W, G.degree (.inr w) : ℝ) / card W) / (card α).factorial)
          · rw [← h_sum_degrees_eq_card_edges, Nat.cast_sum, mul_div,
              div_le_div_iff_of_pos_right (by positivity), mul_le_mul_iff_right₀ (by positivity)]
            exact pow_le_descPochhammer_eval h_avg
          · exact le_card_filter h_le h_avg
        -- counting `v`
        · grw [card_filter_le h_free, mul_le_mul_of_nonneg_right (Nat.choose_le_pow_div ..)
            (sub_nonneg_of_le (Nat.one_le_cast.mpr card_pos))]
      -- take `card α`-th roots in `h`
      rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)] at h
      have h_root : (#G.edgeFinset / card W - card α + 1 : ℝ) ≤
          (card β - 1) ^ (card α : ℝ)⁻¹ * card V / card W ^ (card α : ℝ)⁻¹ := by
        have hlhs_pos : 0 ≤ (#G.edgeFinset / card W - card α + 1 : ℝ) := by
          rwa [← Nat.cast_sum, h_sum_degrees_eq_card_edges, ← sub_nonneg, ← sub_add] at h_avg
        calc (#G.edgeFinset / card W - card α + 1 : ℝ)
          _ = ((#G.edgeFinset / card W - card α + 1 : ℝ) ^ card α) ^ (card α : ℝ)⁻¹ :=
              (Real.pow_rpow_inv_natCast hlhs_pos card_pos.ne').symm
          _ ≤ ((card β - 1) * card V ^ card α / card W) ^ (card α : ℝ)⁻¹ := by
              refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
              rw [le_div_iff₀ (mod_cast card_pos), mul_comm]
              exact h.trans_eq (mul_comm ..)
          _ = (card β - 1) ^ (card α : ℝ)⁻¹ * card V / card W ^ (card α : ℝ)⁻¹ := by
              have hβ : (0 : ℝ) ≤ card β - 1 := sub_nonneg_of_le (Nat.one_le_cast.mpr card_pos)
              rw [Real.div_rpow (by positivity) (by positivity), Real.mul_rpow hβ (by positivity),
                Real.pow_rpow_inv_natCast (by positivity) card_pos.ne']
      -- rearrange into `bound`
      calc (#G.edgeFinset : ℝ)
        _ = card W * (#G.edgeFinset / card W - card α + 1) + (card α - 1) * card W := by
            rw [mul_comm, sub_add, sub_mul, div_mul_cancel₀ _ (by positivity), sub_add_cancel]
        _ ≤ card W * ((card β - 1) ^ (card α : ℝ)⁻¹ * card V / card W ^ (card α : ℝ)⁻¹)
              + (card α - 1) * card W :=
            add_le_add_left (mul_le_mul_of_nonneg_left h_root (Nat.cast_nonneg _)) _
        _ = bound (card V) (card W) (card α) (card β) := by
            rw [bound, Real.rpow_sub (mod_cast card_pos), Real.rpow_one, mul_div_assoc',
              mul_comm (card W : ℝ), mul_div_assoc]

end KovariSosTuran

/-- An upper bound on the Zarankiewicz function.

This is the **Kővári-Sós-Turán theorem**. -/
public theorem zarankiewicz_le (m n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) :
    zarankiewicz m n s t ≤
      ((t - 1) ^ (s⁻¹ : ℝ) * m * n ^ (1 - (s⁻¹ : ℝ)) + (s - 1) * n : ℝ) := by
  have : NeZero s := ⟨Nat.pos_iff_ne_zero.mp hs⟩
  have : NeZero t := ⟨Nat.pos_iff_ne_zero.mp <| hs.trans ht⟩
  rw [← KovariSosTuran.bound, zarankiewicz_le_iff_of_nonneg
    (Fintype.card_fin m) (Fintype.card_fin n) (Fintype.card_fin s) (Fintype.card_fin t) <|
    KovariSosTuran.bound_nonneg m n hs (hs.trans ht)]
  conv =>
    enter [_, _, _, _, 2]
    rw [← Fintype.card_fin m, ← Fintype.card_fin n, ← Fintype.card_fin s, ← Fintype.card_fin t]
  exact fun G _ ↦ KovariSosTuran.card_edgeFinset_le_bound_of_completeBipartiteGraph_free

/-- An upper bound on the symmetric Zarankiewicz function.

This is a corollary of the **Kővári-Sós-Turán theorem**. -/
public theorem symm_zarankiewicz_le (n : ℕ) {s t : ℕ} (hs : 1 ≤ s) (ht : s ≤ t) :
    zarankiewicz n n s t ≤
      ((t - 1) ^ (s : ℝ)⁻¹ * n ^ (2 - (s : ℝ)⁻¹) + (s - 1) * n : ℝ) := by
  have h_one_add_one_sub_inv_card_ne_zero : 1 + (1 - (s : ℝ)⁻¹) ≠ 0 := by
    rw [← add_sub_assoc, one_add_one_eq_two]
    exact sub_ne_zero_of_ne <| ne_of_gt <| s.cast_inv_le_one.trans_lt one_lt_two
  rw [← one_add_one_eq_two, add_sub_assoc,
    Real.rpow_one_add' (by positivity) h_one_add_one_sub_inv_card_ne_zero, ← mul_assoc]
  exact zarankiewicz_le n n hs ht

/-- An upper bound on the extremal numbers of `completeBipartiteGraph α β`.

This is a corollary of the **Kővári-Sós-Turán theorem**. -/
public theorem extremalNumber_completeBipartiteGraph_le
    (n : ℕ) [Nonempty α] (hcard_le : card α ≤ card β) :
    (extremalNumber n (completeBipartiteGraph α β) : ℝ) ≤
      (card β - 1) ^ (card α : ℝ)⁻¹ * n ^ (2 - (card α : ℝ)⁻¹) / 2 + (card α - 1) * n / 2 := by
  have : Nonempty β := card_pos_iff.mp <|  card_pos.trans_le hcard_le
  rw [← add_div, le_div_iff₀' zero_lt_two, ← Nat.cast_two, ← Nat.cast_mul]
  exact (symm_zarankiewicz_le n card_pos hcard_le).trans' <|
    mod_cast two_mul_extremalNumber_le_zarankiewicz_symm rfl rfl

end SimpleGraph

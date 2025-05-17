/-
Copyright (c) 2024 John Talbot and Lian Bremner Tattersall. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Talbot, Lian Bremner Tattersall
-/
import Mathlib.Combinatorics.SimpleGraph.AndrasfaiErdosSos.FiveWheelLike
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
/-!
# Andrasfái-Erdős-Sós Theorem:

We formalize Brandt's proof of the Andrásfai-Erdős-Sós theorem:
 `colorable_of_cliqueFree_lt_minDegree`

If G is Kᵣ₊₁-free and δ(G) > (3r - 4)n/(3r - 1) then G is (r + 1)-colorable.

## References

  B. Andrasfái, P Erdős, V. T. Sós
  **On the connection between chromatic number, maximal clique, and minimal degree of a graph**
  https://doi.org/10.1016/0012-365X(74)90133-2

  S. Brandt **On the structure of graphs with bounded clique number**
  https://doi.org/10.1007/s00493-003-0042-z
-/

local notation "‖" x "‖" => Fintype.card x

variable {k r n i j : ℕ}

private lemma kr_bound (hk : k ≤ r) :
    (2 * r + 2 + k) * n / (2 * r + 2 + k + 3) ≤ (3 * r + 2) * n / (3 * r + 5) := by
  apply (Nat.le_div_iff_mul_le <| Nat.succ_pos _).2
      <| (mul_le_mul_left (2 * r + 2 + k + 2).succ_pos).1 _
  rw [← mul_assoc, mul_comm (2 * r + 2 + k + 3), mul_comm _ (_ * n)]
  apply (Nat.mul_le_mul_right _ (Nat.div_mul_le_self ..)).trans
  nlinarith

open Finset SimpleGraph
variable {α : Type*} {G : SimpleGraph α} [DecidableRel G.Adj] {x : α} {s : Finset α}
/-- Transform lower bound on non-edges into upper bound on edges -/
private lemma card_adj_le_of_le_card_not_adj (hx : i ≤ #(s.filter fun z ↦ ¬ G.Adj x z)) :
    #(s.filter fun z ↦ G.Adj x z) ≤ #s - i := by
  rw [← filter_card_add_filter_neg_card_eq_card (s := s) (fun z ↦ G.Adj x z)]
  rw [add_tsub_assoc_of_le hx]
  exact Nat.le_add_right ..

variable [Fintype α] [DecidableEq α] {W X : Finset α}
/--
Given lower bounds on non-degrees from `W` into `X` and into `α` we can bound degrees over `W`
-/
private lemma sum_degree_le_of_le_not_adj (hx : ∀ x, x ∈ X → i  ≤ #(W.filter fun z ↦ ¬ G.Adj x z))
    (hy : ∀ y, j ≤ #(W.filter fun z ↦ ¬ G.Adj y z)) :
    ∑ w ∈ W, G.degree w ≤ #X * (#W - i) + #Xᶜ * (#W - j) := calc
   _ = ∑ v, #(G.neighborFinset v ∩ W) := by
      simp only [degree, card_eq_sum_ones]
      exact sum_comm' (fun _ _ ↦ by simp [and_comm, adj_comm])
   _ ≤ _ := by
    rw [← union_compl X, sum_union disjoint_compl_right]
    simp_rw [neighborFinset_eq_filter, filter_inter, univ_inter, card_eq_sum_ones X,
      card_eq_sum_ones Xᶜ, sum_mul, one_mul]
    apply add_le_add <;> apply sum_le_sum <;> intro x hx1
    · exact card_adj_le_of_le_card_not_adj <| hx x hx1
    · exact card_adj_le_of_le_card_not_adj <| hy x

namespace SimpleGraph
open Classical in
/-- **Andrasfái-Erdős-Sós**
If `G` is `Kᵣ₊₁`-free and `G.minDegree > (3r - 4)n/(3r - 1)` then `G` is (r + 1)-colorable
e.g. `K₃`-free and `G.minDegree > 2 * n / 5` then `G` is 2-colorable -/
theorem colorable_of_cliqueFree_lt_minDegree (hf : G.CliqueFree (r + 1))
    (hd : (3 * r - 4) * ‖α‖ / (3 * r - 1) < G.minDegree) : G.Colorable r := by
  cases r with
  | zero => simpa using hf
  | succ r =>
  -- There is an edge maximal Kᵣ₊₂-free graph H such that G ≤ H
  obtain ⟨H, hle, hmcf⟩ := @Finite.exists_le_maximal _ _ _ (fun H ↦ H.CliqueFree (r + 2)) G hf
  -- If we can (r + 1)-color H then we can (r + 1)-color G
  apply Colorable.mono_left hle
  by_contra! hnotcol
  -- If H is complete-multipartite and Kᵣ₊₁-free then it is (r + 1)-colorable
  have hn : ¬ H.IsCompleteMultipartite := fun hc ↦ hnotcol <| hc.colorable_of_cliqueFree hmcf.1
-- Since H is maximally Kᵣ₊₂-free and not complete-multipartite it contains a maximal 5-wheel-like
  obtain ⟨v, w₁, w₂, s₁, s₂, hw, hm⟩ :=
    exists_max_isFiveWheelLike_of_max_cliqueFree_not_isCompleteMultipartite hmcf hn
-- The two key sets of vertices are `X`, consisting of all vertices that are common
-- neighbours of all of `s₁ ∩ s₂`,
  let X := {x | ∀ {y}, y ∈ s₁ ∩ s₂ → H.Adj x y}.toFinset
-- and `W` which consists of all vertices of the 5-wheel.
  let W := {v} ∪ ({w₁} ∪ ({w₂} ∪ (s₁ ∪ s₂))) --  insert v <| insert w₁ <| insert w₂ (s₁ ∪ s₂)
-- Any vertex in `X` has at least 3 non-neighbors in `W` (otherwise we can build a bigger wheel)
  have dXle : ∀ x, x ∈ X → 3 ≤ #(W.filter fun z ↦ ¬ H.Adj  x z) := by
    intro z hx
    simp_rw [X, Set.toFinset_setOf, mem_filter, mem_univ, true_and] at hx
    exact hw.three_le_not_adj_of_cliqueFree_max hmcf.1 hx hm
-- Every vertex has at least 1 non-neighbor in `W`.
-- So we have a bound on the degree sum over `W`
-- `∑ w ∈ W, H.degree w ≤  |X| * (|W| - 3) + |Xᶜ| * (|W| - 1)`
  have boundW := sum_degree_le_of_le_not_adj dXle <| hw.one_le_not_adj_of_cliqueFree hmcf.1
-- Since `X` consists of all vertices adjacent to all of `s₁ ∩ s₂`,
-- so any `x ∈ Xᶜ` has at least one non-neighbour in `X`.
  have xcle : ∀ x, x ∈ Xᶜ → 1 ≤ #((s₁ ∩ s₂).filter fun z ↦ ¬ H.Adj  x z) := by
    intro x hx
    apply card_pos.2
    obtain ⟨_, hy⟩ : ∃ y ∈ s₁ ∩ s₂, ¬ H.Adj x y := by
      contrapose! hx
      rw [mem_compl, not_not, Set.mem_toFinset]
      exact hx _
    exact ⟨_, mem_filter.2 hy⟩
-- So we also have a bound on the degree sum over `s₁ ∩ s₂`
-- `∑ w ∈ s₁ ∩ s₂, H.degree w ≤  |Xᶜ| * (|s₁ ∩ s₂| - 1) + |X| * |s₁ ∩ s₂|`
  have boundX := sum_degree_le_of_le_not_adj xcle (fun x ↦ Nat.zero_le _)
  rw [compl_compl, tsub_zero, add_comm] at boundX
  let k := #(s₁ ∩ s₂)
  have krle: (2 * r + k) * ‖α‖ / (2 * r + k + 3) ≤ (3 * r - 1) * ‖α‖ / (3 * r + 2) := by
    cases r with
    | zero   => exact (Nat.not_succ_le_zero _ <| hw.card_inter_lt_of_cliqueFree hmcf.1).elim
    | succ r => apply kr_bound <| Nat.le_of_succ_le_succ <| hw.card_inter_lt_of_cliqueFree hmcf.1
-- Complete the proof by contradiction by showing that `H.minDegree` is too small
  apply H.minDegree.le_lt_asymm (krle.trans' _) <| hd.trans_le <| G.minDegree_le_minDegree hle
  rw [Nat.le_div_iff_mul_le (Nat.add_pos_right _ zero_lt_three)]
  have Wc : #W + k = 2 * r + 3 := hw.card_add_card_inter
  have w3 : 3 ≤ #W := hw.three_le_card
--- Two cases: `s₁ ∩ s₂ = ∅`
  by_cases hst : k = 0
  · rw [hst, add_zero] at Wc ⊢
    rw [← Wc, ← tsub_eq_of_eq_add Wc]
    have Xu : X = univ := by
      apply eq_univ_of_forall
      rw [card_eq_zero] at hst
      intro x; simp [X, hst]
    rw [Xu, card_univ, compl_univ, card_empty, zero_mul, add_zero, mul_comm] at boundW
    apply boundW.trans'
    rw [card_eq_sum_ones, mul_sum, mul_one]
    exact sum_le_sum (fun i _ ↦ H.minDegree_le_degree i)
--- `s₁ ∩ s₂ ≠ ∅`
  · have hap :  #W - 1 + 2 * (k - 1) = #W - 3 + 2 * k := by omega
    calc
    minDegree H * (2 * r + k + 3) ≤ ∑ w ∈ W, H.degree w +  2 * ∑ w ∈ s₁ ∩ s₂, H.degree w := by
        rw [add_assoc, add_comm k, ← add_assoc, ← Wc, add_assoc, ← two_mul, mul_add]
        simp_rw [k, card_eq_sum_ones, ← mul_assoc, mul_sum, mul_one]
        apply add_le_add <;> apply sum_le_sum <;> intro i _
        · exact minDegree_le_degree ..
        · exact mul_comm 2 _ ▸ (Nat.mul_le_mul_left _ <| H.minDegree_le_degree _)
    _ ≤ #X * (#W - 3) + #Xᶜ * (#W - 1) + 2 * (#X * k + #Xᶜ * (k - 1)) :=
          add_le_add boundW <| Nat.mul_le_mul_left _ boundX
    _ = #X * (#W - 3 + 2 * k) + #Xᶜ * ((#W - 1) + 2 * (k - 1)) := by ring_nf
    _ ≤ (2 * r + k) * ‖α‖ := by
        rw [hap, ← add_mul, card_compl, add_tsub_cancel_of_le (card_le_univ _), mul_comm]
        apply Nat.mul_le_mul_right
        rw [two_mul, ← add_assoc]
        apply Nat.add_le_add_right
        rw [tsub_add_eq_add_tsub w3, Wc, Nat.add_sub_cancel_right]

end SimpleGraph

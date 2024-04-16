/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Girth

/-!
# Diameter of a simple graph

This file defines the diameter of a simple graph as the greatest distance between any two vertices
in the graph.
-/

namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}

/- The diameter of a simple graph is a greatest distance between any two vertices. -/
noncomputable def diam (G : SimpleGraph α) : ℕ :=
  sSup {d | ∃ u v : α, d = G.dist u v}

lemma diam_ne_zero_nonempty (h : G.diam ≠ 0) : Nonempty α := by
  contrapose h
  unfold diam
  aesop

lemma not_bddAbove_diam_eq_zero (h : ¬BddAbove {d | ∃ u v : α, d = G.dist u v}) :
    G.diam = 0 := by
  apply Set.infinite_of_not_bddAbove at h
  rw [diam, Set.Infinite.Nat.sSup_eq_zero h]

@[simp]
lemma diam_exists [Nonempty α] : ∃ u v : α, G.dist u v = G.diam := by
  let s := {d | ∃ u v : α, d = G.dist u v}
  let u := Classical.arbitrary α
  by_cases h : BddAbove s
  · have : s.Nonempty := ⟨0, u, u, dist_self.symm⟩
    obtain ⟨u, v, huv⟩ := Nat.sSup_mem this h
    use u, v, huv.symm
  · rw [not_bddAbove_diam_eq_zero h]
    use u, u, dist_self

lemma diam_eq_zero {n : ℕ} :
    G.diam = 0 ↔ ¬BddAbove {d | ∃ u v : α, d = G.dist u v} ∨ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases h' : G = ⊥
    · apply Or.inr h'
    · apply Or.inl
      rw [← edgeSet_eq_empty] at h'
      have : ∃ u v : α, G.Adj u v := by sorry
      sorry
  ·
    sorry

lemma diam_lt {n : ℕ} : G.diam ≤ n ↔ ∀ u v: α, G.dist u v ≤ n := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · intro u v

    sorry
  ·
    sorry

noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  sSup {d | ∃ u v : α, d = G.dist u v}

lemma le_ediam {u v : α} : G.dist u v ≤ G.ediam := by
  apply le_sSup
  tauto

private lemma top_not_mem_of_sup_ne_top {s : Set ℕ∞} (h : sSup s ≠ ⊤) : ⊤ ∉ s := by
  contrapose! h
  rw [sSup_eq_top]
  intros
  use ⊤

variable [Nonempty α]

/- There exists vertices which the distance of attains the diameter. -/
@[simp]
lemma ediam_exists : G.ediam ≠ ⊤ ↔ ∃ (u v : α),  G.dist u v = G.ediam := by
  refine ⟨fun h => ?_, ?_⟩
  unfold ediam at h ⊢
  let s' := WithTop.some ⁻¹' {d : ℕ∞ | ∃ u v : α, d = G.dist u v}
  have nonempty_s' : s'.Nonempty := by
    let v := Classical.arbitrary α
    use 0, v, v
    exact congrArg _ SimpleGraph.dist_self.symm
  have bddAbove_s' : BddAbove s' := by
    apply sSup_eq_top.not.mp at h
    push_neg at h
    rcases h with ⟨ub, ub_lt_top, hub⟩
    use WithTop.untop ub ub_lt_top.ne
    intro a ha
    rw [WithTop.le_untop_iff]
    rw [Set.mem_preimage] at ha
    exact hub a ha
  obtain ⟨u, v, huv⟩ := Nat.sSup_mem nonempty_s' bddAbove_s'
  rw [WithTop.sSup_eq (top_not_mem_of_sup_ne_top h) bddAbove_s']
  use u, v, huv.symm
  aesop

lemma ediam_eq_top_infinite_support (h : G.ediam = ⊤) : Infinite α := by
  rw [ediam, sSup_eq_top] at h
  simp only [Set.mem_setOf_eq] at h
  contrapose! h
  rw [not_infinite_iff_finite] at h
  --apply Finite.exists_max (G.dist)
  sorry

lemma zero_lt_ediam_iff (ht : G.ediam ≠ ⊤) :
    0 < G.ediam ↔ ∃ (u v : α), G.ediam = G.dist u v ∧ G.Reachable u v ∧ u ≠ v := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨u, v, huv⟩ := ediam_exists.mp ht
    rw [← huv, Nat.cast_pos, pos_iff_ne_zero, ne_eq, dist_eq_zero_iff_eq_or_not_reachable.not] at h
    push_neg at h
    use u, v, huv.symm, h.2, h.1
  · obtain ⟨u, v, h⟩ := h
    rw [h.1, Nat.cast_pos]
    apply LT.lt.nat_succ_le (Reachable.pos_dist_of_ne h.2.1 h.2.2)

lemma ediam_le_subgraph_ediam {G' : SimpleGraph α} (hg: G.Connected) (h : G ≤ G') :
    G'.ediam ≤ G.ediam := by
  by_cases ht : G.ediam = ⊤
  · rw [ht]
    apply le_top
  · obtain ⟨u, v, huv⟩ := ediam_exists.mp ht
    by_cases ht' : G'.ediam = ⊤
    · exfalso
      rw [← not_ne_iff, ediam_exists.not] at ht'
      push_neg at ht'
      sorry
    · obtain ⟨u', v', huv'⟩ := ediam_exists.mp ht'
      replace h : G'.dist u' v' ≤ G.dist u' v' := by
        apply dist_le_subgraph_dist h
        rw [connected_iff_exists_forall_reachable] at hg
        obtain ⟨_, hx⟩ := hg
        exact Reachable.trans (hx u').symm (hx v')
      have h' : G.dist u' v' ≤ G.ediam := le_ediam
      rw [← huv, ← huv', Nat.cast_le]
      rw [← ENat.coe_toNat ht, Nat.cast_inj] at huv
      rw [← ENat.coe_toNat ht, Nat.cast_le, ← huv] at h'
      exact LE.le.trans h h'

lemma diam_anti : Antitone (ediam : SimpleGraph α → ℕ∞) := by sorry
  --fun _ _ => diam_le_subgraph_diam

open ENat

theorem girth_le_two_diam_plus_one (h : ¬G.IsAcyclic) : G.girth ≤ 2 * toNat G.ediam + 1 := by
  have hg : ∃ (n : ℕ), ↑n = G.girth := by
    rw [← girth_eq_top, ← ne_eq, WithTop.ne_top_iff_exists] at h
    exact h
  rw [← exists_girth_eq_length] at h
  obtain ⟨v, c, h, h'⟩ := h
  obtain ⟨_, hn⟩ := hg
  rw [← hn, Nat.cast_inj] at h'
  rw [← hn]
  norm_cast
  by_contra
  have hcon : 2 * (toNat G.ediam + 1) ≤ c.length := by omega
  have he : ∃ a b, (c.toSubgraph.coe).dist a b = toNat G.ediam + 1 := by
    sorry
  obtain ⟨a, b, he⟩ := he
  sorry

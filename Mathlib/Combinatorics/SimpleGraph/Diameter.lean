/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Data.ENat.Lattice

/-!
# Diameter of a simple graph

This file defines the diameter of a simple graph as the greatest distance between any two vertices
in the graph.

## Main definitions

- `SimpleGraph.diam` is the graph diameter.

- `SimpleGraph.ediam` is the graph extended diameter.

## Todo

- Prove that `ENat.toNat G.girth ≤ 2 * G.diam + 1` when the diameter is non-zero.

-/

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

/--
The diameter is the greatest distance between any two vertices, with the value `0` in case the
distances are not bounded above.
-/
noncomputable def diam (G : SimpleGraph α) : ℕ :=
  sSup {d | ∃ u v, d = G.dist u v}

lemma nonempty_of_diam_ne_zero (h : G.diam ≠ 0) : Nonempty α := by
  contrapose h
  unfold diam
  aesop

private lemma diam_eq_zero_of_not_bddAbove (h : ¬BddAbove {d | ∃ u v, d = G.dist u v}) :
    G.diam = 0 := by
  apply Set.infinite_of_not_bddAbove at h
  rw [diam, Set.Infinite.Nat.sSup_eq_zero h]

lemma exists_dist_eq_diam [Nonempty α] : ∃ u v, G.dist u v = G.diam := by
  let s := {d | ∃ u v, d = G.dist u v}
  let u := Classical.arbitrary α
  by_cases h : BddAbove s
  · have : s.Nonempty := ⟨0, u, u, dist_self.symm⟩
    obtain ⟨u, v, huv⟩ := Nat.sSup_mem this h
    use u, v, huv.symm
  · exact diam_eq_zero_of_not_bddAbove h ▸ ⟨u, u, dist_self⟩

lemma bddAbove_dist_le_diam (h : BddAbove {d | ∃ u v, d = G.dist u v}) :
    ∀ u v, G.dist u v ≤ G.diam := by
  rw [diam, Nat.sSup_def h]
  aesop

@[simp] lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  unfold diam
  by_cases h : Nonempty α
  · have : {d | ∃ u v, d = (⊥ : SimpleGraph α).dist u v} = {0} :=
      Set.ext_iff.mpr fun _ ↦ ⟨fun ⟨_, _, h⟩ ↦ dist_bot _ _ ▸ h,
      fun h ↦ ⟨Classical.arbitrary α, Classical.arbitrary α, dist_bot _ _ ▸ h⟩⟩
    exact this ▸ csSup_singleton _
  · simp_all

lemma diam_eq_zero : G.diam = 0 ↔ ¬BddAbove {d | ∃ u v, d = G.dist u v} ∨ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · by_cases h' : G = ⊥
    · exact Or.inr h'
    · have : ∃ u v, G.Adj u v := by
        by_contra
        have : G = emptyGraph α := by ext; simp_all
        exact h' (emptyGraph_eq_bot _ ▸ this)
      obtain ⟨u, v, huv⟩ := this
      apply Or.inl
      by_contra h
      have := bddAbove_dist_le_diam h u v
      simp_all [dist_eq_one_iff_adj.mpr huv]
  · cases' h with h h
    · exact diam_eq_zero_of_not_bddAbove h
    · rw [h, diam_bot]

lemma dist_le_diam (h : G.diam ≠ 0) : ∀ u v, G.dist u v ≤ G.diam := by
  intros
  apply le_csSup
  rw [ne_eq, diam_eq_zero] at h
  repeat tauto

lemma diam_mono [Nonempty α] (hg : G.Connected) (hz : G.diam ≠ 0) (h : G ≤ G') :
    G'.diam ≤ G.diam :=
  have ⟨u, v, huv⟩ := G'.exists_dist_eq_diam
  huv ▸ LE.le.trans (dist_le_subgraph_dist h <| hg u v) <| G.dist_le_diam hz u v

/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  sSup {d | ∃ u v : α, d = G.dist u v}

lemma le_ediam {u v : α} : G.dist u v ≤ G.ediam := by
  apply le_sSup
  tauto

/-- The extended diameter is equal to the distance of some vertices iff it is not infinite. -/
lemma ediam_exists [Nonempty α] : G.ediam ≠ ⊤ ↔ ∃ (u v : α),  G.dist u v = G.ediam := by
  refine ⟨fun h ↦ ?_, by aesop⟩
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
    exact hub a ha
  obtain ⟨u, v, huv⟩ := Nat.sSup_mem nonempty_s' bddAbove_s'
  rw [ediam, WithTop.sSup_eq (sup_eq_top_of_top_mem.mt h) bddAbove_s']
  use u, v, huv.symm

lemma zero_lt_ediam_iff [Nonempty α] (ht : G.ediam ≠ ⊤) :
    0 < G.ediam ↔ ∃ (u v : α), G.ediam = G.dist u v ∧ G.Reachable u v ∧ u ≠ v := by
  refine ⟨fun h ↦ ?_, fun ⟨u, v, h⟩ ↦ h.1 ▸ Nat.cast_pos.mpr (h.2.1.pos_dist_of_ne h.2.2)⟩
  obtain ⟨u, v, huv⟩ := ediam_exists.mp ht
  rw [← huv, Nat.cast_pos, pos_iff_ne_zero, ne_eq, dist_eq_zero_iff_eq_or_not_reachable] at h
  push_neg at h
  use u, v, huv.symm, h.2, h.1

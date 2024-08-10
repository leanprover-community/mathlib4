/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.NormNum

/-!
# Diameter of a simple graph

This file defines the diameter of a simple graph as the greatest distance between any two vertices
in the graph.

## Main definitions

- `SimpleGraph.diam` is the graph diameter.

- `SimpleGraph.ediam` is the graph extended diameter.

## Todo

- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1` when the diameter is
  non-zero.

-/

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

section ediam

/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above.
-/
noncomputable def ediam (G : SimpleGraph α) :=
  ⨆ u, ⨆ v, G.edist u v

lemma ediam_def : G.ediam = ⨆ p : (α × α), G.edist p.1 p.2 := by
  rw [ediam, iSup_prod]

lemma edist_le_ediam {u v : α} : G.edist u v ≤ G.ediam :=
  LE.le.trans (le_iSup _ _) <| le_iSup_iff.mpr fun _ h ↦ h u

lemma ediam_eq_top_iff : G.ediam = ⊤ ↔ ∀ b < ⊤, ∃ u v, b < G.edist u v := by
  simp only [ediam, iSup_eq_top, lt_iSup_iff]

lemma nonempty_of_ediam_ne_zero (h : G.ediam ≠ 0) : Nonempty α := by
  contrapose h
  simp [ediam, not_nonempty_iff.mp h]

lemma ediam_eq_top_of_not_connected [Nonempty α] (h : ¬G.Connected) : G.ediam = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push_neg at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam

lemma exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u v, G.edist u v = G.ediam := by
  let f : (α × α) → ℕ∞ := fun p ↦ G.edist p.1 p.2
  convert_to (∃ p : (α × α), f p = ⨆ p : (α × α), f p)
  rw [Prod.exists, ediam_def]
  exact ENat.sSup_mem_of_Nonempty_of_lt_top <| lt_top_iff_ne_top.mpr <| ediam_def ▸ h

lemma exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.ediam := by
  let f : (α × α) → ℕ∞ := fun p ↦ G.edist p.1 p.2
  by_cases h : G.ediam = ⊤
  · have : ⨆ p, f p = ⊤ := by simp only [f, ediam_def ▸ h]
    have : ∃ p, f p = ⊤ := by
      convert_to ⊤ ∈ Set.range f
      rw [← this]
      exact Set.Nonempty.csSup_mem Set.nonempty_of_nonempty_subtype <|
        Finite.Set.finite_replacement f
    simp_all
  · exact exists_edist_eq_ediam_of_ne_top h

lemma diam_mono_of_ne_top [Nonempty α] (h : G ≤ G') (hn : G'.ediam ≠ ⊤) :
    G'.ediam ≤ G.ediam :=
  have ⟨_, _, huv⟩ := G'.exists_edist_eq_ediam_of_ne_top hn
  huv ▸ LE.le.trans (edist_le_subgraph_edist h) <| edist_le_ediam

lemma diam_mono_of_finite [Nonempty α] [Finite α] (h : G ≤ G') :
    G'.ediam ≤ G.ediam :=
  have ⟨_, _, huv⟩ := G'.exists_edist_eq_ediam_of_finite
  huv ▸ LE.le.trans (edist_le_subgraph_edist h) <| edist_le_ediam

lemma zero_lt_ediam_of_nontrivial [Nontrivial α] :
    0 < G.ediam := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ‹_›
  contrapose! huv
  simp only [ediam, nonpos_iff_eq_zero, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact huv u v

@[simp]
lemma ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤ :=
  ediam_eq_top_of_not_connected bot_not_connected

@[simp]
lemma ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1 := by
  sorry

@[simp]
lemma diam_eq_zero : G.ediam = 0 ↔ Subsingleton α := by
  sorry

@[simp]
lemma diam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by
  sorry

end ediam

section diam

/--
The diameter is the greatest distance between any two vertices, with the value `0` in
case the distances are not bounded above.
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat

lemma dist_le_diam (h : G.ediam ≠ ⊤) {u v : α} : G.dist u v ≤ G.diam :=
  ENat.toNat_le_toNat edist_le_ediam h

end diam

end SimpleGraph

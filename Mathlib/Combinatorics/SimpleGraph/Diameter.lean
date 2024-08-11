/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Diameter of a simple graph

This module defines the diameter of a simple graph, which measure the maximum distance between
vertices.

## Main definitions

- `SimpleGraph.ediam` is the graph extended diameter.

- `SimpleGraph.diam` is the graph diameter.

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

lemma ediam_mono_of_ne_top [Nonempty α] (h : G ≤ G') (hn : G'.ediam ≠ ⊤) :
    G'.ediam ≤ G.ediam :=
  have ⟨_, _, huv⟩ := G'.exists_edist_eq_ediam_of_ne_top hn
  huv ▸ LE.le.trans (edist_le_subgraph_edist h) <| edist_le_ediam

lemma ediam_mono_of_finite [Nonempty α] [Finite α] (h : G ≤ G') :
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
  apply le_antisymm ?_ <| ENat.one_le_iff_pos.mpr zero_lt_ediam_of_nontrivial
  apply ediam_def ▸ iSup_le_iff.mpr
  intro p
  by_cases h : (⊤ : SimpleGraph α).Adj p.1 p.2
  · apply le_of_eq <| edist_eq_one_iff_adj.mpr h
  · simp_all

@[simp]
lemma ediam_eq_zero : G.ediam = 0 ↔ Subsingleton α := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · contrapose! h
    apply not_subsingleton_iff_nontrivial.mp at h
    exact ENat.one_le_iff_ne_zero.mp <| ENat.one_le_iff_pos.mpr zero_lt_ediam_of_nontrivial
  · rw [ediam_def, ENat.iSup_eq_zero.mpr]
    simpa [edist_eq_zero_iff.mpr] using subsingleton_iff.mp h

@[simp]
lemma ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by
  refine ⟨fun h₁ ↦ ?_, fun h ↦ h ▸ ediam_top⟩
  ext u v
  refine ⟨fun h ↦ h.ne, fun h₂ ↦ ?_⟩
  apply G.edist_pos_of_ne at h₂
  apply le_of_eq at h₁
  rw [ediam_def, iSup_le_iff] at h₁
  exact edist_eq_one_iff_adj.mp <| le_antisymm (h₁ (u, v)) <| ENat.one_le_iff_pos.mpr h₂

end ediam

section diam

/--
The diameter is the greatest distance between any two vertices, with the value `0` in
case the distances are not bounded above.
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat

lemma diam_def : G.diam = (⨆ p : (α × α), G.edist p.1 p.2).toNat := by
  rw [diam, ediam_def]

lemma dist_le_diam (h : G.ediam ≠ ⊤) {u v : α} : G.dist u v ≤ G.diam :=
  ENat.toNat_le_toNat edist_le_ediam h

lemma nonempty_of_diam_ne_zero (h : G.diam ≠ 0) : Nonempty α := by
  apply G.nonempty_of_ediam_ne_zero
  contrapose! h
  simp [diam, h]

lemma diam_eq_zero_of_not_connected (h : ¬G.Connected) : G.diam = 0 := by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]

lemma ediam_ne_top_of_diam_ne_zero (h : G.diam ≠ 0) : G.ediam ≠ ⊤ :=
  Ne.symm <| ne_of_apply_ne ENat.toNat fun a ↦ h <| id a.symm

lemma exists_dist_eq_diam_of_ne_zero (h : G.diam ≠ 0) :
    ∃ u v, G.dist u v = G.diam := by
  have : Nonempty α := nonempty_of_diam_ne_zero h
  obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top <| ediam_ne_top_of_diam_ne_zero h
  use u, v
  rw [diam, dist, congrArg ENat.toNat huv]

lemma exists_dist_eq_diam_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.dist u v = G.diam := by
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  use u, v
  rw [diam, dist, congrArg ENat.toNat huv]

lemma diam_mono_of_ne_zero (h : G ≤ G') (hn₁ : G'.diam ≠ 0) (hn₂ : G.diam ≠ 0) :
    G'.diam ≤ G.diam :=
  have : Nonempty α := nonempty_of_diam_ne_zero hn₁
  ENat.toNat_le_toNat (ediam_mono_of_ne_top h (ediam_ne_top_of_diam_ne_zero hn₁))
    <| ediam_ne_top_of_diam_ne_zero hn₂

lemma diam_mono_of_finite [Nonempty α] [Finite α] (h : G ≤ G') (hn : G.diam ≠ 0) :
    G'.diam ≤ G.diam :=
  ENat.toNat_le_toNat (ediam_mono_of_finite h) <| ediam_ne_top_of_diam_ne_zero hn

@[simp]
lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  rw [diam, ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl <| ediam_eq_zero.mpr ‹_›
  · exact Or.inr ediam_bot

@[simp]
lemma diam_top [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1 := by
  rw [diam, ediam_top]
  rfl

@[simp]
lemma diam_eq_zero : G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α := by
  rw [diam, ENat.toNat_eq_zero]
  aesop

@[simp]
lemma diam_eq_one [Nontrivial α] : G.diam = 1 ↔ G = ⊤ := by
  rw [diam, ENat.toNat_eq_iff (by decide)]
  exact ediam_eq_one

end diam

end SimpleGraph

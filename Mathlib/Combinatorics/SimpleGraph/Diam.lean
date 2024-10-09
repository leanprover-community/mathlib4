/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Diameter of a simple graph

This module defines the diameter of a simple graph, which measures the maximum distance between
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
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  ⨆ u, ⨆ v, G.edist u v

lemma ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.2 := by
  rw [ediam, iSup_prod]

lemma edist_le_ediam {u v : α} : G.edist u v ≤ G.ediam :=
  le_iSup₂ (f := G.edist) u v

lemma ediam_le_of_edist_le {k : ℕ∞} (h : ∀ u v, G.edist u v ≤ k ) : G.ediam ≤ k :=
  iSup₂_le h

lemma ediam_le_iff {k : ℕ∞} : G.ediam ≤ k ↔ ∀ u v, G.edist u v ≤ k :=
  iSup₂_le_iff

lemma ediam_eq_top : G.ediam = ⊤ ↔ ∀ b < ⊤, ∃ u v, b < G.edist u v := by
  simp only [ediam, iSup_eq_top, lt_iSup_iff]

lemma ediam_eq_zero_of_subsingleton [Subsingleton α] : G.ediam = 0 := by
  rw [ediam_def, ENat.iSup_eq_zero]
  simpa [edist_eq_zero_iff, Prod.forall] using subsingleton_iff.mp ‹_›

lemma nontrivial_of_ediam_ne_zero (h : G.ediam ≠ 0) : Nontrivial α := by
  contrapose! h
  rw [not_nontrivial_iff_subsingleton] at h
  exact ediam_eq_zero_of_subsingleton

lemma ediam_ne_zero [Nontrivial α] : G.ediam ≠ 0 := by
  obtain ⟨u, v, huv⟩ := exists_pair_ne ‹_›
  contrapose! huv
  simp only [ediam, nonpos_iff_eq_zero, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact huv u v

lemma subsingleton_of_ediam_eq_zero (h : G.ediam = 0) : Subsingleton α := by
  contrapose! h
  apply not_subsingleton_iff_nontrivial.mp at h
  exact ediam_ne_zero

lemma ediam_ne_zero_iff_nontrivial :
    G.ediam ≠ 0 ↔ Nontrivial α :=
  ⟨nontrivial_of_ediam_ne_zero, fun _ ↦ ediam_ne_zero⟩

@[simp]
lemma ediam_eq_zero_iff_subsingleton :
    G.ediam = 0 ↔ Subsingleton α :=
  ⟨subsingleton_of_ediam_eq_zero, fun _ ↦ ediam_eq_zero_of_subsingleton⟩

lemma ediam_eq_top_of_not_connected [Nonempty α] (h : ¬G.Connected) : G.ediam = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push_neg at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam

lemma ediam_eq_top_of_not_preconnected (h : ¬G.Preconnected) : G.ediam = ⊤ := by
  cases isEmpty_or_nonempty α
  · exfalso
    exact h <| IsEmpty.forall_iff.mpr trivial
  · apply ediam_eq_top_of_not_connected
    rw [connected_iff]
    tauto

lemma exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u v, G.edist u v = G.ediam :=
  ENat.exists_eq_iSup₂_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
lemma exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.ediam :=
  Prod.exists'.mp <| ediam_def ▸ exists_eq_ciSup_of_finite

@[gcongr]
lemma ediam_anti (h : G ≤ G') : G'.ediam ≤ G.ediam :=
  iSup₂_mono fun _ _ ↦ edist_anti h

@[simp]
lemma ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤ :=
  ediam_eq_top_of_not_connected bot_not_connected

@[simp]
lemma ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1 := by
  apply le_antisymm ?_ <| Order.one_le_iff_pos.mpr <| pos_iff_ne_zero.mpr ediam_ne_zero
  apply ediam_def ▸ iSup_le_iff.mpr
  intro p
  by_cases h : (⊤ : SimpleGraph α).Adj p.1 p.2
  · apply le_of_eq <| edist_eq_one_iff_adj.mpr h
  · simp_all

@[simp]
lemma ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by
  refine ⟨fun h₁ ↦ ?_, fun h ↦ h ▸ ediam_top⟩
  ext u v
  refine ⟨fun h ↦ h.ne, fun h₂ ↦ ?_⟩
  apply G.edist_pos_of_ne at h₂
  apply le_of_eq at h₁
  rw [ediam_def, iSup_le_iff] at h₁
  exact edist_eq_one_iff_adj.mp <| le_antisymm (h₁ (u, v)) <| Order.one_le_iff_pos.mpr h₂

end ediam

section diam

/--
The diameter is the greatest distance between any two vertices, with the value `0` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def diam (G : SimpleGraph α) :=
  G.ediam.toNat

lemma diam_def : G.diam = (⨆ p : α × α, G.edist p.1 p.2).toNat := by
  rw [diam, ediam_def]

lemma dist_le_diam (h : G.ediam ≠ ⊤) {u v : α} : G.dist u v ≤ G.diam :=
  ENat.toNat_le_toNat edist_le_ediam h

lemma nontrivial_of_diam_ne_zero (h : G.diam ≠ 0) : Nontrivial α := by
  apply G.nontrivial_of_ediam_ne_zero
  contrapose! h
  simp [diam, h]

lemma diam_eq_zero_of_not_connected (h : ¬G.Connected) : G.diam = 0 := by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]

lemma diam_eq_zero_of_ediam_eq_top (h : G.ediam = ⊤) : G.diam = 0 := by
  rw [diam, h, ENat.toNat_top]

lemma ediam_ne_top_of_diam_ne_zero (h : G.diam ≠ 0) : G.ediam ≠ ⊤ :=
  mt diam_eq_zero_of_ediam_eq_top  h

lemma exists_dist_eq_diam [Nonempty α] :
    ∃ u v, G.dist u v = G.diam := by
  by_cases h : G.diam = 0
  · simp [h]
  · obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top <| ediam_ne_top_of_diam_ne_zero h
    use u, v
    rw [diam, dist, congrArg ENat.toNat huv]

@[gcongr]
lemma diam_anti_of_ediam_ne_top (h : G ≤ G') (hn : G.ediam ≠ ⊤) : G'.diam ≤ G.diam :=
  ENat.toNat_le_toNat (ediam_anti h) hn

@[simp]
lemma diam_bot : (⊥ : SimpleGraph α).diam = 0 := by
  rw [diam, ENat.toNat_eq_zero]
  cases subsingleton_or_nontrivial α
  · exact Or.inl ediam_eq_zero_of_subsingleton
  · exact Or.inr ediam_bot

@[simp]
lemma diam_top [Nontrivial α] : (⊤ : SimpleGraph α).diam = 1 := by
  rw [diam, ediam_top, ENat.toNat_one]

@[simp]
lemma diam_eq_zero : G.diam = 0 ↔ G.ediam = ⊤ ∨ Subsingleton α := by
  rw [diam, ENat.toNat_eq_zero, or_comm, ediam_eq_zero_iff_subsingleton]

@[simp]
lemma diam_eq_one [Nontrivial α] : G.diam = 1 ↔ G = ⊤ := by
  rw [diam, ENat.toNat_eq_iff one_ne_zero, Nat.cast_one, ediam_eq_one]

end diam

end SimpleGraph

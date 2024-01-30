/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENat.Lattice

/-!
# Girth of a simple graph

This file defines the girth of a simple graph as the length of its smallest cycle, or `∞` if the
graph is acyclic.
-/

namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α} {n : ℕ∞}

/-- The girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is acyclic.
-/
noncomputable def girth (G : SimpleGraph α) : ℕ∞ :=
⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp] lemma le_girth : n ≤ G.girth ↔ ∀ a (w : G.Walk a a), w.IsCycle → n ≤ w.length := by
  simp [girth]

@[simp] lemma girth_eq_top : G.girth = ⊤ ↔ G.IsAcyclic := by simp [girth, IsAcyclic]

protected alias ⟨_, IsAcyclic.girth_eq_top⟩ := girth_eq_top

lemma girth_anti : Antitone (girth : SimpleGraph α → ℕ∞) :=
λ G H h ↦ iInf_mono λ a ↦ iInf₂_mono' λ w hw ↦ ⟨w.mapLe h, hw.mapLe _, by simp⟩

lemma exists_girth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.girth = w.length) ↔ ¬ G.IsAcyclic := by
  refine' ⟨_, λ h ↦ _⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← girth_eq_top, ← Ne.def, girth, iInf_subtype', iInf_sigma', ENat.iInf_coe_ne_top,
      ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

@[simp] lemma girth_bot : girth (⊥ : SimpleGraph α) = ⊤ := by simp

end SimpleGraph

/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.ENat.Lattice

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle, they give `0` or `∞` respectively if the graph is acyclic.
-/

namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α} {n : ℕ∞}

/--
The extended girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is
acyclic.
-/
noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

/--
The girth of a simple graph is the length of its smallest cycle, or junk value `0` if the graph is
acyclic.
-/
noncomputable def girth (G : SimpleGraph α) : ℕ :=
ENat.toNat G.egirth

@[simp] lemma le_egirth : n ≤ G.egirth ↔ ∀ a (w : G.Walk a a), w.IsCycle → n ≤ w.length := by
  simp [egirth]

@[simp] lemma egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic := by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.girth_eq_top⟩ := egirth_eq_top

lemma egirth_anti : Antitone (egirth : SimpleGraph α → ℕ∞) :=
  fun G H h ↦ iInf_mono fun a ↦ iInf₂_mono' fun w hw ↦ ⟨w.mapLe h, hw.mapLe _, by simp⟩

lemma exists_egirth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.egirth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨a, w, hw, _⟩ hG
    exact hG _ hw
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma', ENat.iInf_coe_ne_top,
      ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

lemma three_le_egirth : 3 ≤ G.egirth := by
  by_cases h : G.IsAcyclic
  · rw [← egirth_eq_top] at h
    rw [h]
    apply le_top
  · rw [← exists_egirth_eq_length] at h
    have ⟨_, _, _⟩ := h
    simp_all only [Nat.cast_inj, Nat.ofNat_le_cast, Walk.IsCycle.three_le_length]

@[simp] lemma egirth_bot : egirth (⊥ : SimpleGraph α) = ⊤ := by simp

end SimpleGraph

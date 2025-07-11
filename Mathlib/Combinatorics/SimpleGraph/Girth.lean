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

## TODO

- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1` when the diameter is
  non-zero.

-/

namespace SimpleGraph
variable {α : Type*} {G : SimpleGraph α}

section egirth


/--
The extended girth of a simple graph is the length of its smallest cycle, or `∞` if the graph is
acyclic.
-/
noncomputable def egirth (G : SimpleGraph α) : ℕ∞ :=
  ⨅ a, ⨅ w : G.Walk a a, ⨅ _ : w.IsCycle, w.length

@[simp]
lemma le_egirth {n : ℕ∞} : n ≤ G.egirth ↔ ∀ a (w : G.Walk a a), w.IsCycle → n ≤ w.length := by
  simp [egirth]

lemma egirth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.egirth ≤ w.length :=
  le_egirth.mp le_rfl a w h

@[simp]
lemma egirth_eq_top : G.egirth = ⊤ ↔ G.IsAcyclic := by simp [egirth, IsAcyclic]

protected alias ⟨_, IsAcyclic.egirth_eq_top⟩ := egirth_eq_top

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

end egirth

section girth


/--
The girth of a simple graph is the length of its smallest cycle, or junk value `0` if the graph is
acyclic.
-/
noncomputable def girth (G : SimpleGraph α) : ℕ :=
  G.egirth.toNat

lemma girth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.girth ≤ w.length :=
  ENat.coe_le_coe.mp <| G.egirth.coe_toNat_le_self.trans <| egirth_le_length h

lemma three_le_girth (hG : ¬ G.IsAcyclic) : 3 ≤ G.girth :=
  ENat.toNat_le_toNat three_le_egirth <| egirth_eq_top.not.mpr hG

lemma girth_eq_zero : G.girth = 0 ↔ G.IsAcyclic :=
  ⟨fun h ↦ not_not.mp <| three_le_girth.mt <| by omega, fun h ↦ by simp [girth, h]⟩

protected alias ⟨_, IsAcyclic.girth_eq_zero⟩ := girth_eq_zero

lemma girth_anti {G' : SimpleGraph α} (hab : G ≤ G') (h : ¬ G.IsAcyclic) : G'.girth ≤ G.girth :=
  ENat.toNat_le_toNat (egirth_anti hab) <| egirth_eq_top.not.mpr h

lemma exists_girth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.girth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨by tauto, fun h ↦ ?_⟩
  obtain ⟨_, _, _⟩ := exists_egirth_eq_length.mpr h
  simp_all only [girth, ENat.toNat_coe]
  tauto

@[simp] lemma girth_bot : girth (⊥ : SimpleGraph α) = 0 := by
  simp [girth]

end girth

end SimpleGraph

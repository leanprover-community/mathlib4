/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Diam

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle, they give `0` or `∞` respectively if the graph is acyclic.

## TODO

- Prove that `G.egirth ≤ 2 * G.ediam + 1` and `G.girth ≤ 2 * G.diam + 1` when the diameter is
  non-zero.

-/

@[expose] public section

namespace SimpleGraph
variable {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}

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

set_option backward.isDefEq.respectTransparency false in
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
  simpa using fun _ _ a ↦ Walk.IsCycle.three_le_length a

@[simp] lemma egirth_bot : egirth (⊥ : SimpleGraph α) = ⊤ := by simp

@[gcongr only]
lemma IsContained.egirth_le (h : G ⊑ G') : G'.egirth ≤ G.egirth := by
  by_cases hacyc : G.IsAcyclic
  · simp [hacyc.egirth_eq_top]
  obtain ⟨a, w, hw, hwl⟩ := exists_egirth_eq_length.mpr hacyc
  rw [hwl, ← w.length_map h.some.toHom]
  exact egirth_le_length <| hw.map h.some.injective

@[gcongr only]
lemma Iso.egirth_eq (f : G ≃g G') : G.egirth = G'.egirth :=
  le_antisymm f.isContained'.egirth_le f.isContained.egirth_le

lemma egirth_le_two_ediam_plus_one (h : ¬ G.IsAcyclic) : G.egirth ≤ 2 * G.ediam + 1 := by
  obtain ⟨u, w, hw, hwl⟩ := exists_egirth_eq_length.mpr h
  have half_g_le_edist : ↑(w.length / 2) ≤ G.edist u (w.getVert (w.length / 2)) := by
    have ⟨p,_⟩ := ((w.take (w.length / 2)).reachable).exists_walk_length_eq_edist
    by_contra! hlt; classical
    have ⟨x,_,_,c,c_cycle,c_len⟩ := Walk.IsPath.exists_isCycle_length_le_add_of_ne
      p.bypass_isPath (w.drop (w.length / 2)).reverse.bypass_isPath (by grind [ENat.coe_lt_coe,
      Walk.length_reverse, Walk.length_append, Walk.length_bypass_le_length, Walk.take_length,
      Walk.IsPath.bypass_eq_self, Walk.IsCycle.three_le_length, Walk.length_eq_zero_iff,
      Walk.append_take_drop_eq, Walk.IsCycle.isPath_of_append_right, Walk.IsPath.reverse])
    grind [ENat.coe_lt_coe, Walk.length_bypass_le_length, Walk.length_reverse, egirth_le_length,
    ENat.coe_le_coe, Walk.length_append, Walk.IsCycle.three_le_length, Walk.length_eq_zero_iff,
    Walk.take_length, Walk.append_take_drop_eq, Walk.IsCycle.isPath_of_append_right]
  calc
    G.egirth ≤ 2 * ↑(w.length / 2) + 1 := by rw [hwl]; norm_cast; grind
    _  ≤ 2 * G.ediam + 1 := by gcongr; grind [edist_le_ediam]

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
  ⟨fun h ↦ not_not.mp <| three_le_girth.mt <| by lia, fun h ↦ by simp [girth, h]⟩

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

lemma IsContained.girth_le (h : G ⊑ G') (hG : ¬G.IsAcyclic) : G'.girth ≤ G.girth :=
  ENat.toNat_le_toNat h.egirth_le <| egirth_eq_top.not.mpr hG

lemma Iso.girth_eq (f : G ≃g G') : G.girth = G'.girth := by
  simp [girth, f.egirth_eq]

end girth

end SimpleGraph

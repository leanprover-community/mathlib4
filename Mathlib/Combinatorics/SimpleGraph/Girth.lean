/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.ENat.Lattice

/-!
# Girth of a simple graph

This file defines the girth and the extended girth of a simple graph as the length of its smallest
cycle, they give `0` or `∞` respectively if the graph is acyclic.

## TODO

- Prove that `G.egirth ≤ 2 * G.ediam + 1` when `G` is not acyclic
- Prove that `G.girth ≤ 2 * G.diam + 1` when the diameter is non-zero

-/

@[expose] public section

namespace SimpleGraph
variable {α β : Type*} {G : SimpleGraph α} {G' : SimpleGraph β}

-- #41373
theorem Free.cliqueFree {n : ℕ} {H : SimpleGraph (Fin n)} (h : H.Free G) : G.CliqueFree n := by
  rw [cliqueFree_iff]
  contrapose! h
  exact .trans (.of_le le_top) h

-- #41364
theorem cliqueFree_iff_free_top_fin {n : ℕ} : G.CliqueFree n ↔ (completeGraph (Fin n)).Free G :=
  not_cliqueFree_iff_top_isContained n |>.not_right

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

lemma Walk.IsCircuit.egirth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.egirth ≤ w.length := by
  classical
  by_contra! hlg
  let w' : G.Walk a a := w.cycleBypass
  have hwc' : w'.IsCycle := hwc.isCycle_cycleBypass
  have hwlg' : w'.length < G.egirth := by
    grw [w.length_cycleBypass_le_length]
    exact hlg
  exact not_le_of_gt hwlg' (SimpleGraph.egirth_le_length hwc')

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
  · simp_rw [← egirth_eq_top, ← Ne.eq_def, egirth, iInf_subtype', iInf_sigma',
      ENat.iInf_natCast_ne_top, ← exists_prop, Subtype.exists', Sigma.exists', eq_comm] at h ⊢
    exact ciInf_mem _

lemma three_le_egirth : 3 ≤ G.egirth := by
  simpa using fun _ _ h ↦ h.three_le_length

@[simp] lemma egirth_bot : egirth (⊥ : SimpleGraph α) = ⊤ := by simp

theorem egirth_top (h : 3 ≤ ENat.card α) : egirth (⊤ : SimpleGraph α) = 3 := by
  classical
  refine le_antisymm ?_ three_le_egirth
  obtain ⟨s, hcard⟩ := Cardinal.exists_finset_eq_card <| Cardinal.ofNat_le_toENat.mp h
  obtain ⟨x, y, z, hxy, hxz, hyz, -⟩ := s.card_eq_three.mp hcard.symm
  set w : Walk ⊤ x x := .cons hxy <| .cons hyz <| .cons hxz.symm .nil with hw
  have : w.IsCycle :=
    { edges_nodup := by aesop
      ne_nil := by aesop
      support_nodup := by aesop }
  grw [egirth_le_length this]
  simp [hw]

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

theorem le_egirth_iff_free_cycleGraph {k : ℕ∞} :
    k ≤ G.egirth ↔ ∀ n : ℕ, 3 ≤ n → n < k → (cycleGraph n).Free G := by
  rw [le_egirth]
  refine ⟨fun h n hn hnk hcyc ↦ hnk.not_ge ?_, fun h v p hp ↦ ?_⟩
  · obtain ⟨v, p, hp, rfl⟩ := cycleGraph_isContained_iff hn |>.mp hcyc
    exact h v p hp
  · by_contra! hlt
    apply h p.length hp.three_le_length hlt
    exact cycleGraph_isContained_iff hp.three_le_length |>.mpr ⟨v, p, hp, rfl⟩

theorem free_cycleGraph_of_lt_egirth {n : ℕ} (hle : 3 ≤ n) (hlt : n < G.egirth) :
    (cycleGraph n).Free G :=
  le_egirth_iff_free_cycleGraph.mp (Order.add_one_le_of_lt hlt) n hle ENat.natCast_lt_succ

theorem IsClique.egirth_le_encard {s : Set α} (hs : G.IsClique s) (hcard : 3 ≤ s.encard) :
    G.egirth ≤ s.encard := by
  rcases s.finite_or_infinite with hfin | hinf
  · by_contra! hlt
    have : 3 ≤ s.ncard := ENat.natCast_le_natCast.mp <| hcard.trans_eq hfin.cast_ncard_eq.symm
    have := (free_cycleGraph_of_lt_egirth this <| hfin.cast_ncard_eq.trans_lt hlt).cliqueFree
    exact this hfin.toFinset ⟨by simpa using hs, s.ncard_eq_toFinset_card (hs := hfin).symm⟩
  · simp [hinf]

theorem egirth_ne_three_iff_cliqueFree : G.egirth ≠ 3 ↔ G.CliqueFree 3 := by
  simp_rw [← G.three_le_egirth.lt_iff_ne', ← Nat.cast_ofNat (R := ℕ∞),
    ← ENat.natCast_add_one_le_iff, le_egirth_iff_free_cycleGraph, ENat.lt_natCast_add_one_iff,
    ENat.natCast_le_natCast, cliqueFree_iff_free_top_fin, completeGraph_eq_top,
    ← cycleGraph_three_eq_top]
  grind

end egirth

section girth


/--
The girth of a simple graph is the length of its smallest cycle, or junk value `0` if the graph is
acyclic.
-/
noncomputable def girth (G : SimpleGraph α) : ℕ :=
  G.egirth.toNat

variable (G) in
theorem girth_eq_toNat_egirth : G.girth = G.egirth.toNat :=
  rfl

variable (G) in
theorem natCast_girth_le_egirth : G.girth ≤ G.egirth :=
  G.egirth.natCast_toNat_le_self

theorem natCast_girth_eq_egirth_iff : G.girth = G.egirth ↔ ¬G.IsAcyclic :=
  G.egirth.natCast_toNat_eq_self.trans G.egirth_eq_top.not

theorem girth_eq_iff {n : ℕ} : G.girth = n ↔ G.egirth = n ∨ (n = 0 ∧ G.IsAcyclic) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [girth_eq_toNat_egirth, (three_pos.trans_le <| G.three_le_egirth).ne']
  · simp [girth_eq_toNat_egirth, ENat.toNat_eq_iff, hn]

theorem girth_eq_iff_of_ne_zero {n : ℕ} (hn : n ≠ 0) : G.girth = n ↔ G.egirth = n := by
  simp [girth_eq_iff, hn]

theorem girth_eq_iff_of_not_isAcyclic {n : ℕ} (h : ¬G.IsAcyclic) : G.girth = n ↔ G.egirth = n := by
  simp [girth_eq_iff, h]

@[simp]
theorem le_girth_iff_natCast_le_egirth {n : ℕ} :
    n ≤ G.girth ↔ n ≤ G.egirth ∧ (n = 0 ∨ ¬G.IsAcyclic) := by
  rcases eq_or_ne G.egirth ⊤ with h | h
  · simp [girth_eq_toNat_egirth, egirth_eq_top.mp, h]
  rw [← ENat.natCast_toNat h]
  simp [girth_eq_toNat_egirth, egirth_eq_top.not.mp h]

theorem le_girth {n : ℕ} :
    n ≤ G.girth ↔ (n = 0 ∨ ¬G.IsAcyclic) ∧ ∀ a (w : G.Walk a a), w.IsCycle → n ≤ w.length := by
  simp [and_comm]

lemma girth_le_length {a} {w : G.Walk a a} (h : w.IsCycle) : G.girth ≤ w.length :=
  ENat.natCast_le_natCast.mp <| G.natCast_girth_le_egirth.trans <| egirth_le_length h

lemma three_le_girth (hG : ¬ G.IsAcyclic) : 3 ≤ G.girth :=
  ENat.toNat_le_toNat three_le_egirth <| egirth_eq_top.not.mpr hG

lemma girth_eq_zero : G.girth = 0 ↔ G.IsAcyclic := by
  simp [girth_eq_toNat_egirth, (three_pos.trans_le <| G.three_le_egirth).ne']

protected alias ⟨_, IsAcyclic.girth_eq_zero⟩ := girth_eq_zero

lemma girth_anti {G' : SimpleGraph α} (hab : G ≤ G') (h : ¬ G.IsAcyclic) : G'.girth ≤ G.girth :=
  ENat.toNat_le_toNat (egirth_anti hab) <| egirth_eq_top.not.mpr h

lemma Walk.IsCircuit.girth_le_length {a} {w : G.Walk a a} (hwc : w.IsCircuit) :
    G.girth ≤ w.length :=
  ENat.natCast_le_natCast.mp <| G.natCast_girth_le_egirth.trans <| hwc.egirth_le_length

lemma exists_girth_eq_length :
    (∃ (a : α) (w : G.Walk a a), w.IsCycle ∧ G.girth = w.length) ↔ ¬ G.IsAcyclic := by
  refine ⟨by tauto, fun h ↦ ?_⟩
  obtain ⟨_, _, _⟩ := exists_egirth_eq_length.mpr h
  simp_all only [girth, ENat.toNat_natCast]
  tauto

@[simp] lemma girth_bot : girth (⊥ : SimpleGraph α) = 0 := by
  simp [girth]

theorem girth_top (h : 3 ≤ ENat.card α) : girth (⊤ : SimpleGraph α) = 3 := by
  simp [girth, egirth_top h]

lemma IsContained.girth_le (h : G ⊑ G') (hG : ¬G.IsAcyclic) : G'.girth ≤ G.girth :=
  ENat.toNat_le_toNat h.egirth_le <| egirth_eq_top.not.mpr hG

lemma Iso.girth_eq (f : G ≃g G') : G.girth = G'.girth := by
  simp [girth, f.egirth_eq]

theorem le_girth_iff_free_cycleGraph {k : ℕ} :
    k ≤ G.girth ↔ (k = 0 ∨ ¬G.IsAcyclic) ∧ ∀ n : ℕ, 3 ≤ n → n < k → (cycleGraph n).Free G := by
  simp_rw [le_girth_iff_natCast_le_egirth, and_comm, le_egirth_iff_free_cycleGraph, Nat.cast_lt]

theorem free_cycleGraph_of_lt_girth {n : ℕ} (hle : 3 ≤ n) (hlt : n < G.girth) :
    (cycleGraph n).Free G :=
  free_cycleGraph_of_lt_egirth hle <| by grw [hlt, ← G.natCast_girth_le_egirth]

theorem IsClique.girth_le_encard {s : Set α} (hs : G.IsClique s) (hcard : 3 ≤ s.ncard) :
    G.girth ≤ s.ncard := by
  have := s.finite_of_ncard_pos <| by lia
  grw [← Nat.cast_le (α := ℕ∞), G.natCast_girth_le_egirth, this.cast_ncard_eq, hs.egirth_le_encard]
  grw [← Nat.cast_ofNat, hcard, this.cast_ncard_eq]

theorem girth_ne_three_iff_cliqueFree : G.girth ≠ 3 ↔ G.CliqueFree 3 := by
  simp [egirth_ne_three_iff_cliqueFree, girth_eq_iff_of_ne_zero]

end girth

end SimpleGraph

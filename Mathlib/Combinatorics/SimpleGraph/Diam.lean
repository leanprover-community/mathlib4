/-
Copyright (c) 2024 Rida Hamadani. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rida Hamadani
-/
import Mathlib.Combinatorics.SimpleGraph.Metric

/-!
# Diameter of a simple graph

This module defines the eccentricity of vertices, the diameter, and the radius of a simple graph.

## Main definitions

- `SimpleGraph.eccent`: the eccentricity of a vertex in a simple graph, which is the maximum
  distances between it and the other vertices.

- `SimpleGraph.ediam`: the graph extended diameter, which is the maximum eccentricity.
  It is `ℕ∞`-valued.

- `SimpleGraph.diam`: the graph diameter, an `ℕ`-valued version of `SimpleGraph.ediam`.

- `SimpleGraph.radius`: the graph radius, which is the minimum eccentricity. It is `ℕ∞`-valued.

- `SimpleGraph.center`: the set of vertices with eccentricity equal to the graph's radius.

-/

assert_not_exists Field

namespace SimpleGraph
variable {α : Type*} {G G' : SimpleGraph α}

section eccent

/-- The eccentricity of a vertex is the greatest distance between it and any other vertex. -/
noncomputable def eccent (G : SimpleGraph α) (u : α) : ℕ∞ :=
  ⨆ v, G.edist u v

lemma eccent_def : G.eccent = fun u ↦ ⨆ v, G.edist u v := rfl

lemma edist_le_eccent {u v : α} : G.edist u v ≤ G.eccent u :=
  le_iSup (G.edist u) v

lemma exists_edist_eq_eccent_of_finite [Finite α] (u : α) :
    ∃ v, G.edist u v = G.eccent u :=
  have : Nonempty α := Nonempty.intro u
  exists_eq_ciSup_of_finite

lemma eccent_eq_top_of_not_connected (h : ¬ G.Connected) (u : α) :
    G.eccent u = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push_neg at h
  obtain ⟨v, h⟩ := h u
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable h]
  exact le_iSup (G.edist u) v

lemma eccent_eq_zero_of_subsingleton [Subsingleton α] (u : α) : G.eccent u = 0 := by
  simpa [eccent, edist_eq_zero_iff] using subsingleton_iff.mp ‹_› u

lemma eccent_ne_zero [Nontrivial α] (u : α) : G.eccent u ≠ 0 := by
  obtain ⟨v, huv⟩ := exists_ne ‹_›
  contrapose! huv
  simp only [eccent, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
  exact (huv v).symm

lemma eccent_eq_zero_iff (u : α) : G.eccent u = 0 ↔ Subsingleton α := by
  refine ⟨fun h ↦ ?_, fun _ ↦ eccent_eq_zero_of_subsingleton u⟩
  contrapose! h
  rw [not_subsingleton_iff_nontrivial] at h
  exact eccent_ne_zero u

lemma eccent_pos_iff (u : α) : 0 < G.eccent u ↔ Nontrivial α := by
  rw [pos_iff_ne_zero, ← not_subsingleton_iff_nontrivial, ← eccent_eq_zero_iff]

@[simp]
lemma eccent_bot [Nontrivial α] (u : α) : (⊥ : SimpleGraph α).eccent u = ⊤ :=
  eccent_eq_top_of_not_connected bot_not_connected u

@[simp]
lemma eccent_top [Nontrivial α] (u : α) : (⊤ : SimpleGraph α).eccent u = 1 := by
  apply le_antisymm ?_ <| Order.one_le_iff_pos.mpr <| pos_iff_ne_zero.mpr <| eccent_ne_zero u
  rw [eccent, iSup_le_iff]
  intro v
  cases eq_or_ne u v <;> simp_all [edist_top_of_ne]

lemma eq_top_iff_forall_eccent_eq_one [Nontrivial α] :
    G = ⊤ ↔ ∀ u, G.eccent u = 1 := by
  refine ⟨fun h ↦ h ▸ eccent_top, fun h ↦ ?_⟩
  ext u v
  refine ⟨Adj.ne, fun huv ↦ ?_⟩
  rw [← edist_eq_one_iff_adj]
  apply le_antisymm ((h u).symm ▸ edist_le_eccent)
  rw [Order.one_le_iff_pos, pos_iff_ne_zero, edist_eq_zero_iff.ne]
  exact huv.ne

end eccent

section ediam

/--
The extended diameter is the greatest distance between any two vertices, with the value `⊤` in
case the distances are not bounded above, or the graph is not connected.
-/
noncomputable def ediam (G : SimpleGraph α) : ℕ∞ :=
  ⨆ u, G.eccent u

lemma ediam_eq_iSup_iSup_edist : G.ediam = ⨆ u, ⨆ v, G.edist u v :=
  rfl

lemma ediam_def : G.ediam = ⨆ p : α × α, G.edist p.1 p.2 := by
  rw [ediam, eccent_def, iSup_prod]

lemma eccent_le_ediam {u : α} : G.eccent u ≤ G.ediam :=
  le_iSup G.eccent u

lemma edist_le_ediam {u v : α} : G.edist u v ≤ G.ediam :=
  le_iSup₂ (f := G.edist) u v

lemma ediam_le_of_edist_le {k : ℕ∞} (h : ∀ u v, G.edist u v ≤ k) : G.ediam ≤ k :=
  iSup₂_le h

lemma ediam_le_iff {k : ℕ∞} : G.ediam ≤ k ↔ ∀ u v, G.edist u v ≤ k :=
  iSup₂_le_iff

lemma ediam_eq_top : G.ediam = ⊤ ↔ ∀ b < ⊤, ∃ u v, b < G.edist u v := by
  simp only [ediam, eccent, iSup_eq_top, lt_iSup_iff]

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
  simp only [ediam, eccent, nonpos_iff_eq_zero, ENat.iSup_eq_zero, edist_eq_zero_iff] at huv
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

lemma ediam_eq_top_of_not_connected [Nonempty α] (h : ¬ G.Connected) : G.ediam = ⊤ := by
  rw [connected_iff_exists_forall_reachable] at h
  push_neg at h
  obtain ⟨_, hw⟩ := h Classical.ofNonempty
  rw [eq_top_iff, ← edist_eq_top_of_not_reachable hw]
  exact edist_le_ediam

lemma ediam_eq_top_of_not_preconnected (h : ¬ G.Preconnected) : G.ediam = ⊤ := by
  cases isEmpty_or_nonempty α
  · exfalso
    exact h <| IsEmpty.forall_iff.mpr trivial
  · apply ediam_eq_top_of_not_connected
    rw [connected_iff]
    tauto

lemma preconnected_of_ediam_ne_top (h : G.ediam ≠ ⊤) : G.Preconnected :=
  Not.imp_symm G.ediam_eq_top_of_not_preconnected h

lemma connected_of_ediam_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) : G.Connected :=
  G.connected_iff.mpr ⟨preconnected_of_ediam_ne_top h, ‹_›⟩

lemma exists_eccent_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u, G.eccent u = G.ediam :=
  ENat.exists_eq_iSup_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
lemma exists_eccent_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u, G.eccent u = G.ediam :=
  exists_eq_ciSup_of_finite

lemma exists_edist_eq_ediam_of_ne_top [Nonempty α] (h : G.ediam ≠ ⊤) :
    ∃ u v, G.edist u v = G.ediam :=
  ENat.exists_eq_iSup₂_of_lt_top h.lt_top

-- Note: Neither `Finite α` nor `G.ediam ≠ ⊤` implies the other.
lemma exists_edist_eq_ediam_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.ediam :=
  Prod.exists'.mp <| ediam_def ▸ exists_eq_ciSup_of_finite

/-- In a finite graph with nontrivial vertex set, the graph is connected
if and only if the extended diameter is not `⊤`.
See `connected_of_ediam_ne_top` for one of the implications without
the finiteness assumptions -/
lemma connected_iff_ediam_ne_top [Nonempty α] [Finite α] : G.Connected ↔ G.ediam ≠ ⊤ :=
  have ⟨u, v, huv⟩ := G.exists_edist_eq_ediam_of_finite
  ⟨fun h ↦ huv ▸ edist_ne_top_iff_reachable.mpr (h u v),
   fun h ↦ G.connected_of_ediam_ne_top h⟩

@[gcongr]
lemma ediam_anti (h : G ≤ G') : G'.ediam ≤ G.ediam :=
  iSup₂_mono fun _ _ ↦ edist_anti h

@[simp]
lemma ediam_bot [Nontrivial α] : (⊥ : SimpleGraph α).ediam = ⊤ :=
  ediam_eq_top_of_not_connected bot_not_connected

@[simp]
lemma ediam_top [Nontrivial α] : (⊤ : SimpleGraph α).ediam = 1 := by
  simp [ediam]

@[simp]
lemma ediam_eq_one [Nontrivial α] : G.ediam = 1 ↔ G = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ h ▸ ediam_top⟩
  rw [eq_top_iff_forall_eccent_eq_one]
  intro u
  apply le_antisymm (h ▸ eccent_le_ediam)
  rw [Order.one_le_iff_pos, pos_iff_ne_zero]
  exact eccent_ne_zero u

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

lemma diam_eq_zero_of_not_connected (h : ¬ G.Connected) : G.diam = 0 := by
  cases isEmpty_or_nonempty α
  · rw [diam, ediam, ciSup_of_empty, bot_eq_zero']; rfl
  · rw [diam, ediam_eq_top_of_not_connected h, ENat.toNat_top]

lemma diam_eq_zero_of_ediam_eq_top (h : G.ediam = ⊤) : G.diam = 0 := by
  rw [diam, h, ENat.toNat_top]

lemma ediam_ne_top_of_diam_ne_zero (h : G.diam ≠ 0) : G.ediam ≠ ⊤ :=
  mt diam_eq_zero_of_ediam_eq_top h

lemma exists_dist_eq_diam [Nonempty α] :
    ∃ u v, G.dist u v = G.diam := by
  by_cases h : G.diam = 0
  · simp [h]
  · obtain ⟨u, v, huv⟩ := exists_edist_eq_ediam_of_ne_top <| ediam_ne_top_of_diam_ne_zero h
    use u, v
    rw [diam, dist, congrArg ENat.toNat huv]

lemma diam_ne_zero_of_ediam_ne_top [Nontrivial α] (h : G.ediam ≠ ⊤) : G.diam ≠ 0 :=
  have ⟨_, _, hne⟩ := exists_pair_ne ‹_›
  pos_iff_ne_zero.mp <|
    lt_of_lt_of_le ((connected_of_ediam_ne_top h).pos_dist_of_ne hne) <| dist_le_diam h

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

lemma diam_eq_zero_iff_ediam_eq_top [Nontrivial α] : G.diam = 0 ↔ G.ediam = ⊤ := by
  rw [← not_iff_not]
  exact ⟨ediam_ne_top_of_diam_ne_zero, diam_ne_zero_of_ediam_ne_top⟩

/-- A finite and nontrivial graph is connected if and only if its diameter is not zero.
See also `connected_iff_ediam_ne_top` for the extended diameter version. -/
lemma connected_iff_diam_ne_zero [Finite α] [Nontrivial α] : G.Connected ↔ G.diam ≠ 0 := by
  rw [connected_iff_ediam_ne_top, not_iff_not, diam_eq_zero_iff_ediam_eq_top]

end diam

section radius

/-- The radius of a simple graph is the minimum eccentricity of any vertex. -/
noncomputable def radius (G : SimpleGraph α) : ℕ∞ :=
  ⨅ u, G.eccent u

lemma radius_eq_iInf_iSup_edist : G.radius = ⨅ u, ⨆ v, G.edist u v :=
  rfl

lemma radius_le_eccent {u : α} : G.radius ≤ G.eccent u :=
  iInf_le G.eccent u

lemma exists_eccent_eq_radius [Nonempty α] : ∃ u, G.eccent u = G.radius  :=
  ENat.exists_eq_iInf G.eccent

lemma exists_edist_eq_radius_of_finite [Nonempty α] [Finite α] :
    ∃ u v, G.edist u v = G.radius := by
  obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
  obtain ⟨v, hv⟩ := G.exists_edist_eq_eccent_of_finite w
  use w, v
  rw [hv, hw]

lemma radius_eq_top_of_not_connected (h : ¬ G.Connected) : G.radius = ⊤ := by
  simp [radius, eccent_eq_top_of_not_connected h]

lemma radius_eq_top_of_isEmpty [IsEmpty α] : G.radius = ⊤ :=
  iInf_of_empty G.eccent

lemma radius_ne_top_iff [Nonempty α] [Finite α] : G.radius ≠ ⊤ ↔ G.Connected := by
  refine ⟨Not.imp_symm radius_eq_top_of_not_connected, fun h ↦ ?_⟩
  obtain ⟨u, v, huv⟩ := G.exists_edist_eq_radius_of_finite
  rw [← huv, edist_ne_top_iff_reachable]
  exact h u v

lemma radius_ne_zero_of_nontrivial [Nontrivial α] : G.radius ≠ 0 := by
  rw [← ENat.one_le_iff_ne_zero]
  apply le_iInf
  simp [ENat.one_le_iff_ne_zero, G.eccent_ne_zero]

lemma radius_eq_zero_iff : G.radius = 0 ↔ Nonempty α ∧ Subsingleton α := by
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨_, _⟩ ↦ ?_⟩
  · contrapose! h
    simp [radius, not_nonempty_iff.mp h]
  · contrapose! h
    simp [not_subsingleton_iff_nontrivial.mp h, radius_ne_zero_of_nontrivial]
  · rw [radius, ENat.iInf_eq_zero]
    use Classical.ofNonempty
    simpa [eccent] using Subsingleton.elim _

lemma radius_le_ediam [Nonempty α] : G.radius ≤ G.ediam :=
  iInf_le_iSup

lemma ediam_le_two_mul_radius [Finite α] : G.ediam ≤ 2 * G.radius := by
  cases isEmpty_or_nonempty α
  · rw [radius_eq_top_of_isEmpty]
    exact le_top
  · by_cases h : G.Connected
    · obtain ⟨w, hw⟩ := G.exists_eccent_eq_radius
      obtain ⟨_, _, h⟩ := G.exists_edist_eq_ediam_of_ne_top (connected_iff_ediam_ne_top.mp h)
      apply le_trans (h ▸ G.edist_triangle (v := w))
      rw [two_mul]
      exact hw ▸ add_le_add (G.edist_comm ▸ G.edist_le_eccent) G.edist_le_eccent
    · rw [G.radius_eq_top_of_not_connected h]
      exact le_top

lemma radius_eq_ediam_iff [Nonempty α] :
    G.radius = G.ediam ↔ ∃ e, ∀ u, G.eccent u = e := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · use G.radius
    intro u
    exact le_antisymm (h ▸ eccent_le_ediam) radius_le_eccent
  · obtain ⟨e, h⟩ := h
    have ediam_eq : G.ediam = e :=
      le_antisymm (iSup_le fun u ↦ (h u).le) ((h Classical.ofNonempty) ▸ eccent_le_ediam)
    rw [ediam_eq]
    exact le_antisymm ((h Classical.ofNonempty) ▸ radius_le_eccent) (le_iInf fun u ↦ (h u).ge)

@[simp]
lemma radius_bot [Nontrivial α] : (⊥ : SimpleGraph α).radius = ⊤ :=
  radius_eq_top_of_not_connected bot_not_connected

@[simp]
lemma radius_top [Nontrivial α] : (⊤ : SimpleGraph α).radius = 1 := by
  simp [radius]

end radius

section center

/-- The center of a simple graph is the set of vertices with eccentricity equal to the radius. -/
def center (G : SimpleGraph α) : Set α :=
  {u | G.eccent u = G.radius}

lemma center_nonempty [Nonempty α] : G.center.Nonempty :=
  exists_eccent_eq_radius

lemma mem_center_iff (u : α) : u ∈ G.center ↔ G.eccent u = G.radius := .rfl

lemma center_eq_univ_iff_radius_eq_ediam [Nonempty α] :
    G.center = Set.univ ↔ G.radius = G.ediam := by
  rw [radius_eq_ediam_iff, ← Set.univ_subset_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · use G.radius
    exact fun _ ↦ h trivial
  · obtain ⟨e, h⟩ := h
    intro u hu
    rw [mem_center_iff, h u]
    exact le_antisymm (le_iInf fun u ↦ (h u).ge) ((h Classical.ofNonempty) ▸ radius_le_eccent)

lemma center_eq_univ_of_subsingleton [Subsingleton α] : G.center = Set.univ := by
  rw [Set.eq_univ_iff_forall]
  intro u
  rw [mem_center_iff, eccent_eq_zero_of_subsingleton u, eq_comm, radius_eq_zero_iff]
  tauto

lemma center_bot : (⊥ : SimpleGraph α).center = Set.univ := by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff, eccent_bot, radius_bot]

lemma center_top : (⊤ : SimpleGraph α).center = Set.univ := by
  cases subsingleton_or_nontrivial α
  · exact center_eq_univ_of_subsingleton
  · rw [Set.eq_univ_iff_forall]
    intro u
    rw [mem_center_iff, eccent_top, radius_top]

end center

end SimpleGraph

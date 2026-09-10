/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.IncidenceHypergraph.Basic
public import Mathlib.Data.Sym.Sym2
public import Mathlib.Data.Set.Card

/-!
# Incidence graphs

This file defines multigraphs by extending `IncidenceHypergraph` with a pairing of the two
incidences of each edge. The two incidences remain distinct for a loop.

## Main definitions

* `IncidenceGraph`: the incidence graph structure.

## Notation

Within the `IncidenceGraph` scope, `V(G)`, `I(G)`, and `E(G)` denote the vertex, incidence,
and edge sets.

-/

@[expose] public section

open Set IncidenceHypergraph

/-- An incidence based multigraph definition that extends the incidence based hypergraph definition.
-/
structure IncidenceGraph (ν ι ε : Type*) extends IncidenceHypergraph ν ι ε where
  /-- Every edge has an incidence associated with it. -/
  edgeMap_range : range edgeMap' = edgeSet
  /-- The other incidence of the same edge. -/
  other' : incidenceSet → incidenceSet
  /-- The two incidences of an edge are distinct, including for a loop. -/
  other'_ne : ∀ i, other' i ≠ i
  /-- The other incidence is associated with the same edge. -/
  edgeMap'_other' : ∀ i, edgeMap' (other' i) = edgeMap' i
  /-- Every incidence of an edge is one of its two paired incidences. -/
  edgeMap'_eq : ∀ i j, edgeMap' i = edgeMap' j → j = i ∨ j = other' i

variable {ν ι ε : Type*} {G H : IncidenceGraph ν ι ε} {u v w x : ν} {e : ε} {i j : ι}

namespace IncidenceGraph

/-- `V(G)` denotes the `vertexSet` of an incidence graph `G`. -/
scoped notation "V(" G ")" => IncidenceHypergraph.vertexSet (IncidenceGraph.toIncidenceHypergraph G)

/-- `I(G)` denotes the `incidenceSet` of an incidence graph `G`. -/
scoped notation "I(" G ")" =>
  IncidenceHypergraph.incidenceSet (IncidenceGraph.toIncidenceHypergraph G)

/-- `E(G)` denotes the `edgeSet` of a IncidenceGraph `G`. -/
scoped notation "E(" G ")" => IncidenceHypergraph.edgeSet (IncidenceGraph.toIncidenceHypergraph G)

/-! ## Other incidence -/

open Classical in
noncomputable def other [Nonempty ι] (i : ι) : ι :=
  if h : i ∈ I(G) then G.other' ⟨i, h⟩ else Classical.arbitrary ι

lemma other_ne [Nonempty ι] (hi : i ∈ I(G)) : G.other i ≠ i := by
  simp only [other, hi, ↓reduceDIte, ne_eq]
  exact Subtype.coe_ne_coe.mpr <| G.other'_ne ⟨i, hi⟩

lemma other_mem [Nonempty ι] (hi : i ∈ I(G)) : G.other i ∈ I(G) := by
  simp only [other, hi, ↓reduceDIte, Subtype.coe_prop]

@[simp]
lemma edgeMap_other [Nonempty ι] [Nonempty ε] (hi : i ∈ I(G)) :
    G.edgeMap (G.other i) = G.edgeMap i := by
  simp only [edgeMap, other, ↓reduceDIte, hi, ↓reduceDIte, Subtype.coe_prop, Subtype.coe_eta]
  exact G.edgeMap'_other' ⟨i, hi⟩

lemma edgeMap_eq [Nonempty ι] [Nonempty ε] (hi : i ∈ I(G)) (hj : j ∈ I(G)) :
    G.edgeMap i = G.edgeMap j → j = i ∨ j = G.other i := by
  simp only [edgeMap, other, ↓reduceDIte, hi, hj]
  grind [G.edgeMap'_eq ⟨i, hi⟩ ⟨j, hj⟩]

@[simp]
lemma other'_eq_other [Nonempty ι] (i : I(G)) : G.other' i = G.other i := by
  simp [other]

@[simp]
lemma other_other [Nonempty ι] [Nonempty ε] (hi : i ∈ I(G)) : G.other (G.other i) = i :=
  G.edgeMap_eq hi (G.other_mem (G.other_mem hi))
    ((G.edgeMap_other hi).symm.trans (G.edgeMap_other (G.other_mem hi)).symm) |>.resolve_right
    (G.other_ne (G.other_mem hi))

/-! ### endSet -/

lemma endSet_encard_le_two : (G.endSet e).encard ≤ 2 := by
  obtain h | ⟨u, i, hi, rfl⟩ := (G.endSet e).eq_empty_or_nonempty
  · simp [h]
  refine (encard_le_encard (t := {G.attach' i, G.attach' (G.other' i)}) ?_).trans ?_
  · rintro v ⟨j, hj, rfl⟩
    obtain rfl | rfl := G.edgeMap'_eq i j (hi.trans hj.symm) <;> simp
  simpa only [encard_singleton, one_add_one_eq_two] using
    encard_insert_le {G.attach' (G.other' i)} (G.attach' i)

/-! ## IsLink

The inherited `IsLink` predicate uses two distinct incidences of an edge. The pairing axioms
ensure these are precisely the two incidences of that edge, so its endpoints are unique up to
exchange, as in `Graph.IsLink`. Their attached vertices may coincide, giving a loop.
-/

/-- The two paired incidences give a link, even when their attached vertices coincide. -/
lemma isLink_attach_other' (i : I(G)) :
    G.IsLink (G.edgeMap' i) (G.attach' i) (G.attach' (G.other' i)) :=
  ⟨i, G.other' i, (G.other'_ne i).symm, rfl, G.edgeMap'_other' i, rfl, rfl⟩

lemma edge_mem_iff_exists_isLink : e ∈ E(G) ↔ ∃ u v, G.IsLink e u v := by
  refine ⟨fun he ↦ ?_, fun ⟨_, _, h⟩ ↦ h.edge_mem⟩
  obtain ⟨i, rfl⟩ := G.edgeMap_range.symm ▸ he
  exact ⟨_, _, isLink_attach_other' i⟩

end IncidenceGraph

namespace IncidenceHypergraph.IsLink

lemma endSet_eq (h : G.IsLink e u v) : G.endSet e = {u, v} := by
  refine subset_antisymm ?_ h.pair_subset_endSet
  obtain ⟨i, j, hij, hi, hj, rfl, rfl⟩ := h
  obtain rfl : j = G.other' i := (G.edgeMap'_eq i j (hi.trans hj.symm)).resolve_left hij.symm
  rintro _ ⟨k, hk, rfl⟩
  obtain rfl | hk' := G.edgeMap'_eq i k (hi.trans hk.symm)
  · exact mem_insert _ _
  exact mem_insert_of_mem _ (congrArg G.attach' hk')

lemma left_eq_or_eq (h : G.IsLink e u v) (h' : G.IsLink e w x) : u = w ∨ u = x := by
  obtain ⟨a, b, _, ha, _, rfl, rfl⟩ := h
  obtain ⟨c, d, hcd, hc, hd, rfl, rfl⟩ := h'
  have hd' : d = G.other' c := (G.edgeMap'_eq c d (hc.trans hd.symm)).resolve_left hcd.symm
  obtain rfl | ha' := G.edgeMap'_eq c a (hc.trans ha.symm)
  · exact Or.inl rfl
  exact Or.inr (congrArg G.attach' (ha'.trans hd'.symm))

lemma right_eq_or_eq (h : G.IsLink e u v) (h' : G.IsLink e w x) : v = w ∨ v = x :=
  h.symm.left_eq_or_eq h'

lemma left_eq_of_right_ne (h : G.IsLink e u v) (h' : G.IsLink e w x) (hux : u ≠ w) : u = x :=
  (h.left_eq_or_eq h').resolve_left hux

lemma right_unique (h : G.IsLink e u v) (h' : G.IsLink e u x) : v = x := by
  obtain rfl | rfl := h.right_eq_or_eq h'.symm
  · rfl
  obtain rfl | rfl := h'.right_eq_or_eq h.symm <;> rfl

lemma left_unique (h : G.IsLink e u x) (h' : G.IsLink e v x) : u = v :=
  h.symm.right_unique h'.symm

lemma eq_and_eq_or_eq_and_eq (h : G.IsLink e u v) (h' : G.IsLink e w x) :
    u = w ∧ v = x ∨ u = x ∧ v = w := by
  obtain rfl | rfl := h.left_eq_or_eq h'
  · simp [h.right_unique h']
  simp [h'.symm.right_unique h]

lemma isLink_iff (h : G.IsLink e u v) : G.IsLink e w x ↔ u = w ∧ v = x ∨ u = x ∧ v = w := by
  refine ⟨h.eq_and_eq_or_eq_and_eq, ?_⟩
  rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · assumption
  exact h.symm

lemma isLink_iff_sym2_eq (h : G.IsLink e u v) : G.IsLink e w x ↔ s(u, v) = s(w, x) := by
  rw [h.isLink_iff, Sym2.eq_iff]

end IncidenceHypergraph.IsLink

namespace IncidenceGraph

/-! ## Extensionality -/

@[ext]
lemma ext (hV : V(G) = V(H)) (hI : I(G) = I(H)) (hE : E(G) = E(H))
    (hEdge : ∀ (i : ι) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)), G.edgeMap' ⟨i, hiG⟩ = H.edgeMap' ⟨i, hiH⟩)
    (hAttach : ∀ (i : ι) (hiG : i ∈ I(G)) (hiH : i ∈ I(H)),
      G.attach' ⟨i, hiG⟩ = H.attach' ⟨i, hiH⟩) : G = H := by
  have hBase : G.toIncidenceHypergraph = H.toIncidenceHypergraph :=
    IncidenceHypergraph.ext hV hI hE hEdge hAttach
  cases G with | mk G hG Gother hnG heG huG =>
  cases H with | mk H hH Hother hnH heH huH =>
  cases hBase
  obtain rfl : Gother = Hother :=
    funext fun i ↦ ((huG i (Hother i) (heH i).symm).resolve_left (hnH i)).symm
  rfl

end IncidenceGraph

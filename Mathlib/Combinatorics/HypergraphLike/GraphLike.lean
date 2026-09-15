/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.HypergraphLike.Basic

/-!
# Graph-like structures with two incidences per edge

`HyperGraphLike.GraphLike` requires exactly two incidences per active edge, including a source
and a target, and supplies the operation exchanging them. This file develops its incidence
and link API.
-/

@[expose] public section

open Set Function

namespace HyperGraphLike

variable {V I E Gr : Type*} {G : Gr} [HyperGraphLike V I E Gr] {u u' v v' w : V} {i j : I} {e f : E}

section GraphLike

/-- A graph-like object `G` is `GraphLike` if every edge present in `G` has exactly
two incidences, including a source incidence and a target incidence. The operation exchanging the
two incidences is supplied as data, so it can be used without making a classical choice. -/
class GraphLike (G : Gr) where
  /-- The other incidence of the same edge. -/
  other' : I(G) → I(G)
  /-- Exchanging incidences preserves their edge. -/
  toEdge_other' (i : I(G)) : toEdge G (other' i) = toEdge G i
  /-- The two incidences of an edge are distinct, even when their endpoints coincide. -/
  other'_ne (i : I(G)) : other' i ≠ i
  /-- Every incidence of an edge is one of its two paired incidences. -/
  toEdge_eq : ∀ i j, toEdge G i = toEdge G j → j = i ∨ j = other' i
  /-- Every edge present in the structure has a source incidence. -/
  exists_isSource_of_mem_edgeSet ⦃e : E⦄ :
    e ∈ E(G) → ∃ i : I(G), (toEdge G i : E) = e ∧ IsSource G (i : I)
  /-- Every edge present in the structure has a target incidence. -/
  exists_isTarget_of_mem_edgeSet ⦃e : E⦄ :
    e ∈ E(G) → ∃ i : I(G), (toEdge G i : E) = e ∧ IsTarget G (i : I)

/-- Construct a `GraphLike` instance from two-element incidence fibres, using classical choice for
the other incidence. Supply `GraphLike.other'` directly when this operation should compute. -/
@[instance_reducible]
noncomputable def GraphLike.ofOrderEqTwo (order_eq_two : ∀ ⦃e : E⦄, e ∈ E(G) → order G e = 2)
    (exists_isSource : ∀ ⦃e : E⦄, e ∈ E(G) → ∃ i : I(G), toEdge G i = e ∧ IsSource G (i : I))
    (exists_isTarget : ∀ ⦃e : E⦄, e ∈ E(G) → ∃ i : I(G), toEdge G i = e ∧ IsTarget G (i : I)) :
    GraphLike G := by
  have exists_other (i : I(G)) : ∃ j : I(G), toEdge G j = toEdge G i ∧ j ≠ i := by
    have h : 1 < order G (toEdge G i : E) := by
      rw [order_eq_two (toEdge G i).property]
      decide
    obtain ⟨j, k, hj, hk, hjk⟩ := one_lt_encard_iff.mp h
    obtain rfl | hji := eq_or_ne j i
    · exact ⟨k, Subtype.ext hk, fun hki ↦ hjk hki.symm⟩
    · exact ⟨j, Subtype.ext hj, hji⟩
  refine {
    other' i := (exists_other i).choose
    toEdge_other' i := (exists_other i).choose_spec.1
    other'_ne i := (exists_other i).choose_spec.2
    toEdge_eq i j hij := ?_
    exists_isSource_of_mem_edgeSet := exists_isSource
    exists_isTarget_of_mem_edgeSet := exists_isTarget }
  obtain ⟨a, b, hab, hf⟩ := encard_eq_two.mp (order_eq_two (toEdge G i).property)
  have hm (k : I(G)) (hk : toEdge G k = toEdge G i) : k = a ∨ k = b := by
    simpa using (show k ∈ ({a, b} : Set I(G)) from hf ▸ congrArg Subtype.val hk)
  have hi := hm i rfl
  have hj := hm j hij.symm
  have ho := hm _ (exists_other i).choose_spec.1
  have hn := (exists_other i).choose_spec.2
  grind

/-- Construct a `GraphLike` instance from order two and source and target incidences specified
using `edgeMap`, choosing the other incidence classically. -/
@[instance_reducible]
noncomputable def GraphLike.ofOrderEqTwoOfEdgeMap [Nonempty E]
    (order_eq_two : ∀ ⦃e : E⦄, e ∈ E(G) → order G e = 2)
    (exists_isSource : ∀ ⦃e : E⦄, e ∈ E(G) → ∃ i, edgeMap G i = e ∧ IsSource G i)
    (exists_isTarget : ∀ ⦃e : E⦄, e ∈ E(G) → ∃ i, edgeMap G i = e ∧ IsTarget G i) : GraphLike G :=
  GraphLike.ofOrderEqTwo order_eq_two (fun e he ↦ by
    obtain ⟨i, hie, hs⟩ := exists_isSource he
    exact ⟨⟨i, hs.mem⟩, (toEdge_eq_edgeMap ⟨i, hs.mem⟩).trans hie, hs⟩) (fun e he ↦ by
    obtain ⟨i, hie, ht⟩ := exists_isTarget he
    exact ⟨⟨i, ht.mem⟩, (toEdge_eq_edgeMap ⟨i, ht.mem⟩).trans hie, ht⟩)

variable [GraphLike G]

open GraphLike

lemma order_eq_two (he : e ∈ E(G)) : order G e = 2 := by
  obtain ⟨i, hi, _⟩ := exists_isSource_of_mem_edgeSet he
  refine encard_eq_two.mpr ⟨i, other' i, (other'_ne i).symm, ?_⟩
  ext j
  rw [← hi]
  refine ⟨fun hj ↦ toEdge_eq i j (Subtype.ext hj.symm), ?_⟩
  rintro (rfl | rfl)
  · rfl
  exact congrArg Subtype.val (toEdge_other' i)

lemma edgeMap_surjOn [Nonempty E] (G : Gr) [GraphLike G] : SurjOn (edgeMap G) I(G) E(G) :=
  edgeMap_surjOn_iff.mpr fun e he ↦ by simp [order_eq_two he]

lemma edgeMap_range [Nonempty E] (G : Gr) [GraphLike G] :
    range (fun i : I(G) ↦ edgeMap G (i : I)) = E(G) :=
  edgeMap_range_of_order_pos fun e he ↦ by simp [order_eq_two he]

lemma edgeMap_image_incs [Nonempty E] (G : Gr) [GraphLike G] : edgeMap G '' I(G) = E(G) :=
  edgeMap_image_incs_of_order_pos fun e he ↦ by simp [order_eq_two he]

open Classical in
/-- The other incidence of the same edge, with an arbitrary value outside `I(G)`. -/
noncomputable def other [Nonempty I] (G : Gr) [GraphLike G] (i : I) : I :=
  if hi : i ∈ I(G) then other' ⟨i, hi⟩ else Classical.arbitrary I

lemma other_mem [Nonempty I] (hi : i ∈ I(G)) : other G i ∈ I(G) := by
  simpa only [other, dite_eq_left hi] using (other' ⟨i, hi⟩).property

lemma other_ne [Nonempty I] (hi : i ∈ I(G)) : other G i ≠ i := by
  simpa only [other, dite_eq_left hi] using Subtype.coe_ne_coe.mpr (other'_ne ⟨i, hi⟩)

@[simp]
lemma edgeMap_other [Nonempty I] [Nonempty E] (hi : i ∈ I(G)) :
    edgeMap G (other G i) = edgeMap G i := by
  simpa only [toEdge_eq_edgeMap, other, dite_eq_left hi] using
    congrArg Subtype.val (toEdge_other' ⟨i, hi⟩)

/-- The fiber of an active graph incidence consists of it and its other incidence. -/
lemma edgeFiber_edgeMap [Nonempty I] [Nonempty E] (hi : i ∈ I(G)) :
    edgeFiber G (edgeMap G i) = {i, other G i} := by
  refine (((finite_singleton (other G i)).insert i).eq_of_subset_of_encard_le
    (pair_subset_iff.mpr ⟨mem_edgeFiber.mpr ⟨hi, rfl⟩,
      mem_edgeFiber.mpr ⟨other_mem hi, edgeMap_other hi⟩⟩) ?_).symm
  simp only [← order_eq_encard_edgeFiber, order_eq_two (edgeMap_mem hi),
    encard_pair (other_ne hi).symm, le_refl]

lemma isUniform_two (G : Gr) [GraphLike G] : IsUniform G 2 := fun he ↦ order_eq_two he

lemma order_le_two : order G e ≤ 2 := by
  by_cases he : e ∈ E(G)
  · exact (order_eq_two he).le
  simp [order_of_notMem_edges he]

lemma exists_isSource_of_mem_edgeSet [Nonempty E] (he : e ∈ E(G)) :
    ∃ i, edgeMap G i = e ∧ IsSource G i := by
  obtain ⟨i, hi, hs⟩ := GraphLike.exists_isSource_of_mem_edgeSet he
  exact ⟨i, (toEdge_eq_edgeMap i).symm.trans hi, hs⟩

lemma exists_isTarget_of_mem_edgeSet [Nonempty E] (he : e ∈ E(G)) :
    ∃ i, edgeMap G i = e ∧ IsTarget G i := by
  obtain ⟨i, hi, ht⟩ := GraphLike.exists_isTarget_of_mem_edgeSet he
  exact ⟨i, (toEdge_eq_edgeMap i).symm.trans hi, ht⟩

lemma exists_pair_edgeMap_iff [Nonempty E] (he : e ∈ E(G)) :
    ∃ i j, i ≠ j ∧ ∀ x, x ∈ I(G) ∧ edgeMap G x = e ↔ x = i ∨ x = j := by
  simpa [order_eq_encard_edgeFiber, encard_eq_two, Set.ext_iff] using order_eq_two he

@[simp]
lemma other_other [Nonempty I] (hi : i ∈ I(G)) : other G (other G i) = i := by
  let j : I(G) := ⟨i, hi⟩
  have hj : other' (other' j) = j :=
    toEdge_eq j (other' (other' j)) ((toEdge_other' (other' j)).trans (toEdge_other' j)).symm
      |>.resolve_right (other'_ne _)
  rw [other, dite_eq_left (other_mem hi)]
  simpa only [other, dite_eq_left hi] using congrArg Subtype.val hj

lemma other_injOn [Nonempty I] : InjOn (other G) I(G) := fun i hi j hj hij ↦ by
  simpa only [other_other hi, other_other hj] using congrArg (other G) hij

@[simp]
lemma other_inj [Nonempty I] (hi : i ∈ I(G)) (hj : j ∈ I(G)) :
    other G i = other G j ↔ i = j := other_injOn.eq_iff hi hj

lemma edgeMap_eq_iff [Nonempty I] [Nonempty E] (hi : i ∈ I(G)) (hj : j ∈ I(G)) :
    edgeMap G i = edgeMap G j ↔ i = j ∨ i = other G j := by
  simpa only [mem_edgeFiber, hi, true_and, mem_insert_iff, mem_singleton_iff] using
    Iff.of_eq (congrArg (i ∈ ·) (edgeFiber_edgeMap hj))

lemma exists_isLink_of_mem_edgeSet (he : e ∈ E(G)) : ∃ u v, IsLink G e u v := by
  obtain ⟨i, hei, hs⟩ := GraphLike.exists_isSource_of_mem_edgeSet he
  obtain ⟨j, hej, ht⟩ := GraphLike.exists_isTarget_of_mem_edgeSet he
  obtain rfl | hij := eq_or_ne i j
  · let b := other' i
    have hb : (toEdge G b : E) = e := (congrArg Subtype.val (toEdge_other' i)).trans hei
    obtain hbs | hbt := mem_incs_iff.mp b.property
    · exact ⟨_, _, isLink_iff.mpr ⟨b, i, other'_ne i, hbs, ht, hb, rfl, hei, rfl⟩⟩
    exact ⟨_, _, isLink_iff.mpr ⟨i, b, (other'_ne i).symm, hs, hbt, hei, rfl, hb, rfl⟩⟩
  exact ⟨_, _, isLink_iff.mpr ⟨i, j, hij, hs, ht, hei, rfl, hej, rfl⟩⟩

lemma mem_edges_iff_exists_isLink : e ∈ E(G) ↔ ∃ u v, IsLink G e u v :=
  ⟨exists_isLink_of_mem_edgeSet, fun ⟨_, _, h⟩ ↦ h.edge_mem⟩

lemma edges_eq_setOf_exists_isLink (G : Gr) [GraphLike G] : E(G) = {e | ∃ u v, IsLink G e u v} :=
  ext fun _ ↦ mem_edges_iff_exists_isLink

lemma edges_eq_empty_iff_forall_not_isLink : E(G) = ∅ ↔ ∀ e u v, ¬ IsLink G e u v := by
  simp [eq_empty_iff_forall_notMem, mem_edges_iff_exists_isLink]

lemma edges_eq_empty_iff_forall_not_adj : E(G) = ∅ ↔ ∀ u v, ¬ Adj G u v := by
  simp only [edges_eq_empty_iff_forall_not_isLink, adj_iff', not_exists]
  exact ⟨fun h u v e ↦ h e u v, fun h e u v ↦ h u v e⟩

lemma one_lt_order_iff : 1 < order G e ↔ ∃ u v, IsLink G e u v :=
  ⟨fun h ↦ exists_isLink_of_mem_edgeSet (mem_edges_of_order_pos (lt_trans zero_lt_one h)),
    fun ⟨_, _, h⟩ ↦ h.one_lt_order⟩

@[grind <=]
lemma IsLink.eq_or_eq_of_isLink (h : IsLink G e u v) (h' : IsLink G e u' v') :
    u = u' ∧ v = v' ∨ u = v' ∧ v = u' :=
  h.eq_or_eq_of_isLink_of_order_eq_two h' (order_eq_two h.edge_mem)

lemma IsLink.left_eq_or_eq (h : IsLink G e u v) (h' : IsLink G e u' v') : u = u' ∨ u = v' :=
  (h.eq_or_eq_of_isLink h').imp And.left And.left

lemma IsLink.right_eq_or_eq (h : IsLink G e u v) (h' : IsLink G e u' v') : v = u' ∨ v = v' :=
  (h.eq_or_eq_of_isLink h').symm.imp And.right And.right

lemma IsLink.left_eq_of_right_ne (h : IsLink G e u v) (h' : IsLink G e u' v') (hne : u ≠ u') :
    u = v' :=
  (h.left_eq_or_eq h').resolve_left hne

lemma IsLink.right_unique (h : IsLink G e u v) (h' : IsLink G e u w) : v = w :=
  h.right_unique_of_order_eq_two h' (order_eq_two h.edge_mem)

lemma IsLink.left_unique (h : IsLink G e u w) (h' : IsLink G e v w) : u = v :=
  h.left_unique_of_order_eq_two h' (order_eq_two h.edge_mem)

lemma IsLink.isLink_iff_eq (h : IsLink G e u v) : IsLink G e u w ↔ w = v :=
  ⟨fun h' ↦ h'.right_unique h, fun hw ↦ hw ▸ h⟩

lemma IsLink.incVerts_eq (h : IsLink G e u v) : incVerts G e = {u, v} :=
  h.incVerts_eq_of_order_eq_two (order_eq_two h.edge_mem)

lemma IsLink.mem_incVerts_iff (h : IsLink G e u v) : w ∈ incVerts G e ↔ w = u ∨ w = v := by
  simp [h.incVerts_eq]

lemma IsLink.eq_of_mem_incVerts_of_ne (h : IsLink G e u v) (hw : w ∈ incVerts G e) (hne : w ≠ u) :
    w = v :=
  (h.mem_incVerts_iff.mp hw).resolve_left hne

lemma mem_edges_iff_incVerts_nonempty : e ∈ E(G) ↔ (incVerts G e).Nonempty := by
  refine ⟨fun he ↦ ?_, fun ⟨v, hv⟩ ↦ mem_edges_of_mem_incVerts hv⟩
  obtain ⟨u, v, h⟩ := exists_isLink_of_mem_edgeSet he
  exact ⟨u, h.left_mem_incVerts⟩

lemma eq_or_eq_or_eq_of_mem_incVerts (hu : u ∈ incVerts G e) (hv : v ∈ incVerts G e)
    (hw : w ∈ incVerts G e) : u = v ∨ u = w ∨ v = w := by
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet (mem_edges_of_mem_incVerts hu)
  rw [h.mem_incVerts_iff] at hu hv hw
  grind

/-- Every edge of a graph with a single vertex links that vertex to itself. -/
lemma isLink_iff_of_verts_eq_singleton (hV : V(G) = {v}) :
    IsLink G e u w ↔ e ∈ E(G) ∧ u = v ∧ w = v := by
  refine ⟨fun h ↦ ⟨h.edge_mem, ?_, ?_⟩, ?_⟩
  · simpa [hV] using h.left_mem
  · simpa [hV] using h.right_mem
  rintro ⟨he, rfl, rfl⟩
  obtain ⟨x, y, h⟩ := exists_isLink_of_mem_edgeSet he
  obtain rfl : x = w := by simpa [hV] using h.left_mem
  obtain rfl : y = x := by simpa [hV] using h.right_mem
  exact h

lemma adj_iff_of_verts_eq_singleton (hV : V(G) = {v}) :
    Adj G u w ↔ E(G).Nonempty ∧ u = v ∧ w = v := by
  simp only [adj_iff', isLink_iff_of_verts_eq_singleton hV, exists_and_right, nonempty_def]

lemma incVerts_encard_le_two : (incVerts G e).encard ≤ 2 :=
  encard_incVerts_le_order.trans order_le_two

lemma edgeMap_preimage_singleton_injOn_of_GraphLike [Nonempty E] :
    InjOn (fun e ↦ edgeMap G ⁻¹' {e}) E(G) :=
  edgeMap_preimage_singleton_injOn (G := G) fun e he ↦ by simp [order_eq_two he]

end GraphLike

end HyperGraphLike

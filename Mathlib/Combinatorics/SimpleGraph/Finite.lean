/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Sym.Card

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of `edgeSet`, `neighborSet` and `incidenceSet` and proves some
of their basic properties. It also defines the notion of a locally finite graph, which is one
whose vertices have finite degree.

The design for finiteness is that each definition takes the smallest finiteness assumption
necessary. For example, `SimpleGraph.neighborFinset v` only requires that `v` have
finitely many neighbors.

## Main definitions

* `SimpleGraph.edgeFinset` is the `Finset` of edges in a graph, if `edgeSet` is finite
* `SimpleGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
  if `neighborSet` is finite
* `SimpleGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
  if `incidenceSet` is finite

## Naming conventions

If the vertex type of a graph is finite, we refer to its cardinality as `CardVerts`
or `card_verts`.

## Implementation notes

* A locally finite graph is one with instances `Π v, Fintype (G.neighborSet v)`.
* Given instances `DecidableRel G.Adj` and `Fintype V`, then the graph
  is locally finite, too.
-/


open Finset Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {e : Sym2 V}

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
abbrev edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet

@[norm_cast]
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _

variable {G}

theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset

theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

/-- Mapping an edge to a finite set produces a finset of size `2`. -/
theorem card_toFinset_mem_edgeFinset [DecidableEq V] (e : G.edgeFinset) :
    (e : Sym2 V).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp

theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by simp

theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by simp

@[mono, gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

@[mono, gcongr]
alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

@[simp]
theorem edgeFinset_bot : (⊥ : SimpleGraph V).edgeFinset = ∅ := by simp [edgeFinset]

@[simp]
theorem edgeFinset_sup [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V] :
    (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by simp [edgeFinset]

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] :
    (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset := by simp [edgeFinset]

lemma disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂ := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

lemma edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

lemma edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]

theorem edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet :=
  Set.toFinset_card _

@[simp]
theorem edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset

variable [Fintype V]

@[simp]
theorem edgeFinset_top [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset = ({e | ¬e.IsDiag} : Finset _) := by simp [← coe_inj]

/-- The complete graph on `n` vertices has `n.choose 2` edges. -/
theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [Set.toFinset_card, edgeSet_top, Set.coe_setOf, ← Sym2.card_subtype_not_diag]

/-- Any graph on `n` vertices has at most `n.choose 2` edges. -/
theorem card_edgeFinset_le_card_choose_two : #G.edgeFinset ≤ (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

namespace Iso

variable {G} {W : Type*} {G' : SimpleGraph W}

theorem card_edgeFinset_eq (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    #G.edgeFinset = #G'.edgeFinset := by
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset]
  exact f.mapEdgeSet

end Iso

section FiniteAt

/-!
## Finiteness at a vertex

This section contains definitions and lemmas concerning vertices that
have finitely many adjacent vertices.  We denote this condition by
`Fintype (G.neighborSet v)`.

We define `G.neighborFinset v` to be the `Finset` version of `G.neighborSet v`.
Use `neighborFinset_eq_filter` to rewrite this definition as a `Finset.filter` expression.
-/

variable (v) [Fintype (G.neighborSet v)]

/-- `G.neighborFinset v` is the `Finset` version of `G.neighborSet v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset

theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset

theorem notMem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

@[deprecated (since := "2025-05-23")]
alias not_mem_neighborFinset_self := notMem_neighborFinset_self

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| notMem_neighborFinset_self _ _

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| notMem_neighborFinset_self _ _

/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ := #(G.neighborFinset v)

@[simp]
theorem card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v := rfl

@[simp]
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

theorem degree_pos_iff_mem_support : 0 < G.degree v ↔ v ∈ G.support := by
  rw [G.degree_pos_iff_exists_adj v, mem_support]

theorem degree_eq_zero_iff_notMem_support : G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v, Nat.pos_iff_ne_zero, not_ne_iff]

@[deprecated (since := "2025-05-23")]
alias degree_eq_zero_iff_not_mem_support := degree_eq_zero_iff_notMem_support

theorem degree_eq_zero_of_subsingleton {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)]
    (h : Subsingleton V) : G.degree v = 0 := by
  have := G.degree_pos_iff_exists_adj v
  simp_all [subsingleton_iff_forall_eq v]

theorem degree_eq_one_iff_unique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] :
    G.degree v = 1 ↔ ∃! w : V, G.Adj v w := by
  rw [degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]

theorem nontrivial_of_degree_ne_zero {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
    (h : G.degree v ≠ 0) : Nontrivial V := by
  apply not_subsingleton_iff_nontrivial.mp
  by_contra
  simp_all [degree_eq_zero_of_subsingleton]

theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v))]

instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

/-- This is the `Finset` version of `incidenceSet`. -/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset

@[simp]
theorem card_incidenceSet_eq_degree [DecidableEq V] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]
  simp

@[simp]
theorem card_incidenceFinset_eq_degree [DecidableEq V] : #(G.incidenceFinset v) = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

@[simp]
theorem mem_incidenceFinset [DecidableEq V] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset

theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v = {e ∈ G.edgeFinset | v ∈ e} := by
  ext e
  induction e
  simp [mk'_mem_incidenceSet_iff]

theorem incidenceFinset_subset [DecidableEq V] [Fintype G.edgeSet] :
    G.incidenceFinset v ⊆ G.edgeFinset :=
  Set.toFinset_subset_toFinset.mpr (G.incidenceSet_subset v)

/-- The degree of a vertex is at most the number of edges. -/
theorem degree_le_card_edgeFinset [Fintype G.edgeSet] :
    G.degree v ≤ #G.edgeFinset := by
  classical
  rw [← card_incidenceFinset_eq_degree]
  exact card_le_card (G.incidenceFinset_subset v)

variable {G v}

/-- If `G ≤ H` then `G.degree v ≤ H.degree v` for any vertex `v`. -/
lemma degree_le_of_le {H : SimpleGraph V} [Fintype (H.neighborSet v)] (hle : G ≤ H) :
    G.degree v ≤ H.degree v := by
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card fun v hv => hle hv

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set. -/
abbrev LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)

variable [LocallyFinite G]

/-- A locally finite simple graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.degree v = d

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  h v

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl, h v]

end LocallyFinite

section Finite

variable [Fintype V]

instance neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  @Subtype.fintype _ (· ∈ G.neighborSet v)
    (by
      simp_rw [mem_neighborSet]
      infer_instance)
    _

theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = ({w | G.Adj v w} : Finset _) := by ext; simp

theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_diff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (completeGraph V).degree v = Fintype.card V - 1 := by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v), card_univ]

@[simp]
theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  simp_rw [degree, neighborFinset_eq_filter, bot_adj, filter_false]
  exact Finset.card_empty

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  simp

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegree_le_degree`
and `le_minDegree_of_forall_le_degree`. -/
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untopD 0 (univ.image fun v => G.degree v).min

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v := by
  obtain ⟨t, ht : _ = _⟩ := min_of_nonempty (univ_nonempty.image fun v => G.degree v)
  obtain ⟨v, _, rfl⟩ := mem_image.mp (mem_of_min ht)
  exact ⟨v, by simp [minDegree, ht]⟩

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v := by
  obtain ⟨t, ht⟩ := Finset.min_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.min_le_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [minDegree, ht]

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

/-- If there are no vertices then the `minDegree` is zero. -/
@[simp]
lemma minDegree_of_isEmpty [DecidableRel G.Adj] [IsEmpty V] : G.minDegree = 0 := by
  rw [minDegree, WithTop.untopD_eq_self_iff]
  simp

variable {G} in
/-- If `G` is a subgraph of `H` then `G.minDegree ≤ H.minDegree`. -/
lemma minDegree_le_minDegree {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) : G.minDegree ≤ H.minDegree := by
  by_cases hne : Nonempty V
  · apply le_minDegree_of_forall_le_degree
    exact fun v ↦ (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)
  · push_neg at hne
    simp

/-- In a nonempty graph, the minimal degree is less than the number of vertices. -/
theorem minDegree_lt_card [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree < Fintype.card V := by
  obtain ⟨v, hδ⟩ := G.exists_minimal_degree_vertex
  rw [hδ, ← card_neighborFinset_eq_degree, ← card_univ]
  have h : v ∉ G.neighborFinset v :=
    (G.mem_neighborFinset v v).not.mpr (G.loopless v)
  contrapose! h
  rw [eq_of_subset_of_card_le (subset_univ _) h]
  exact mem_univ v

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, true_and] at ht₂
  rcases ht₂ with ⟨v, rfl⟩
  refine ⟨v, ?_⟩
  rw [maxDegree, ht, WithBot.unbotD_coe]

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [maxDegree, ht, WithBot.unbotD_coe]

@[simp]
lemma maxDegree_of_isEmpty [DecidableRel G.Adj] [IsEmpty V] : G.maxDegree = 0 := by
  rw [maxDegree, univ_eq_empty, image_empty, max_empty, WithBot.unbotD_bot]

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : IsEmpty V
  · simp
  · push_neg at hV
    obtain ⟨_, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ h _

@[simp]
lemma maxDegree_bot_eq_zero : (⊥ : SimpleGraph V).maxDegree = 0 :=
  Nat.le_zero.1 <| maxDegree_le_of_forall_degree_le _ _ (by simp)

@[simp]
lemma minDegree_le_maxDegree [DecidableRel G.Adj] : G.minDegree ≤ G.maxDegree := by
  by_cases he : IsEmpty V
  · simp
  · push_neg at he
    exact he.elim fun v ↦ (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)

@[simp]
lemma minDegree_bot_eq_zero : (⊥ : SimpleGraph V).minDegree = 0 :=
  Nat.le_zero.1 <| (minDegree_le_maxDegree _).trans (by simp)

theorem degree_lt_card_verts [DecidableRel G.Adj] (v : V) : G.degree v < Fintype.card V := by
  classical
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  exact ⟨v, by simp, Finset.subset_univ _⟩

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero. -/
theorem maxDegree_lt_card_verts [DecidableRel G.Adj] [Nonempty V] :
    G.maxDegree < Fintype.card V := by
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  rw [hv]
  apply G.degree_lt_card_verts v

theorem card_commonNeighbors_le_degree_left [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left

theorem card_commonNeighbors_le_degree_right [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  simp_rw [commonNeighbors_symm _ v w, card_commonNeighbors_le_degree_left]

theorem card_commonNeighbors_lt_card_verts [DecidableRel G.Adj] (v w : V) :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

/-- If the condition `G.Adj v w` fails, then `card_commonNeighbors_le_degree` is
the best we can do in general. -/
theorem Adj.card_commonNeighbors_lt_degree {G : SimpleGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  rw [← Set.toFinset_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use w
  constructor
  · rw [Set.mem_toFinset]
    apply notMem_commonNeighbors_right
  · rw [Finset.insert_subset_iff]
    constructor
    · simpa
    · rw [neighborFinset, Set.toFinset_subset_toFinset]
      exact G.commonNeighbors_subset_neighborSet_left _ _

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  simp [Finset.card_sdiff, h]

end Finite

section Support

variable {s : Set V} [DecidablePred (· ∈ s)] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma edgeFinset_subset_sym2_of_support_subset (h : G.support ⊆ s) :
    G.edgeFinset ⊆ s.toFinset.sym2 := by
  simp_rw [subset_iff, Sym2.forall,
    mem_edgeFinset, mem_edgeSet, mk_mem_sym2_iff, Set.mem_toFinset]
  intro _ _ hadj
  exact ⟨h ⟨_, hadj⟩, h ⟨_, hadj.symm⟩⟩

instance : DecidablePred (· ∈ G.support) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | ∃ w, G.Adj v w })

theorem map_edgeFinset_induce [DecidableEq V] :
    (G.induce s).edgeFinset.map (Embedding.subtype s).sym2Map
      = G.edgeFinset ∩ s.toFinset.sym2 := by
  simp_rw [Finset.ext_iff, Sym2.forall, mem_inter, mk_mem_sym2_iff, mem_map, Sym2.exists,
    Set.mem_toFinset, mem_edgeSet, comap_adj, Embedding.sym2Map_apply, Embedding.coe_subtype,
    Sym2.map_pair_eq, Sym2.eq_iff]
  intro v w
  constructor
  · rintro ⟨x, y, hadj, ⟨hv, hw⟩ | ⟨hw, hv⟩⟩
    all_goals rw [← hv, ← hw]
    · exact ⟨hadj, x.prop, y.prop⟩
    · exact ⟨hadj.symm, y.prop, x.prop⟩
  · intro ⟨hadj, hv, hw⟩
    use ⟨v, hv⟩, ⟨w, hw⟩, hadj
    tauto

theorem map_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    (G.induce s).edgeFinset.map (Embedding.subtype s).sym2Map = G.edgeFinset := by
  classical
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

/-- If the support of the simple graph `G` is a subset of the set `s`, then the induced subgraph of
`s` has the same number of edges as `G`. -/
theorem card_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    #(G.induce s).edgeFinset = #G.edgeFinset := by
  rw [← map_edgeFinset_induce_of_support_subset h, card_map]

theorem card_edgeFinset_induce_support :
    #(G.induce G.support).edgeFinset = #G.edgeFinset :=
  card_edgeFinset_induce_of_support_subset subset_rfl

theorem map_neighborFinset_induce [DecidableEq V] (v : s) :
    ((G.induce s).neighborFinset v).map (.subtype (· ∈ s)) = G.neighborFinset v ∩ s.toFinset := by
  ext; simp

theorem map_neighborFinset_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    ((G.induce s).neighborFinset v).map (.subtype s) = G.neighborFinset v := by
  classical
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

/-- If the neighbor set of a vertex `v` is a subset of `s`, then the degree of the vertex in the
induced subgraph of `s` is the same as in `G`. -/
theorem degree_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    (G.induce s).degree v = G.degree v := by
  simp_rw [← card_neighborFinset_eq_degree,
    ← map_neighborFinset_induce_of_neighborSet_subset h, card_map]

/-- If the support of the simple graph `G` is a subset of the set `s`, then the degree of vertices
in the induced subgraph of `s` are the same as in `G`. -/
theorem degree_induce_of_support_subset (h : G.support ⊆ s) (v : s) :
    (G.induce s).degree v = G.degree v :=
  degree_induce_of_neighborSet_subset <| (G.neighborSet_subset_support v).trans h

@[simp]
theorem degree_induce_support (v : G.support) :
    (G.induce G.support).degree v = G.degree v :=
  degree_induce_of_support_subset subset_rfl v

end Support

section Map

variable [Fintype V] {W : Type*} [Fintype W] [DecidableEq W]

@[simp]
theorem edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.map f).edgeFinset = G.edgeFinset.map f.sym2Map := by
  rw [Finset.map_eq_image, ← Set.toFinset_image, Set.toFinset_inj]
  exact G.edgeSet_map f

theorem card_edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(G.map f).edgeFinset = #G.edgeFinset := by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

end Map

end SimpleGraph

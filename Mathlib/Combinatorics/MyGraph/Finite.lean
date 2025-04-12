/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
import Mathlib.Algebra.Ring.Defs
import Mathlib.Combinatorics.MyGraph.Maps
import Mathlib.Data.Finset.Max
import Mathlib.Data.Sym.Card

/-!
# Definitions for finite and locally finite graphs

This file defines finite versions of `edgeSet`, `neighborSet` and `incidenceSet` and proves some
of their basic properties. It also defines the notion of a locally finite graph, which is one
whose vertices have finite degree.

The design for finiteness is that each definition takes the smallest finiteness assumption
necessary. For example, `MyGraph.neighborFinset v` only requires that `v` have
finitely many neighbors.

## Main definitions

* `MyGraph.edgeFinset` is the `Finset` of edges in a graph, if `edgeSet` is finite
* `MyGraph.neighborFinset` is the `Finset` of vertices adjacent to a given vertex,
   if `neighborSet` is finite
* `MyGraph.incidenceFinset` is the `Finset` of edges containing a given vertex,
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

namespace MyGraph

variable {V : Type*} (G : MyGraph V) {e : Sym2 V}

section EdgeFinset

variable {G₁ G₂ : MyGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

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

--theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp
@[gcongr]
theorem edgeFinset_mono (h : G₁ ≤ G₂) : G₁.edgeFinset ⊆ G₂.edgeFinset  := by simp [h]

--theorem edgeFinset_strict_mono (h : G₁ < G₂) : G₁.edgeFinset ⊂ G₂.edgeFinset := by simp [h]

-- @[gcongr] alias ⟨_, edgeFinset_mono⟩ := edgeFinset_subset_edgeFinset

-- alias ⟨_, edgeFinset_strict_mono⟩ := edgeFinset_ssubset_edgeFinset

attribute [mono] edgeFinset_mono --edgeFinset_strict_mono

@[simp]
theorem edgeFinset_bot : (⊥ : MyGraph V).edgeFinset = ∅ := by simp [edgeFinset]

@[simp]
theorem edgeFinset_sup [Fintype (edgeSet (G₁ ⊔ G₂))] [DecidableEq V] :
    (G₁ ⊔ G₂).edgeFinset = G₁.edgeFinset ∪ G₂.edgeFinset := by simp [edgeFinset]

@[simp]
theorem edgeFinset_inf [DecidableEq V] : (G₁ ⊓ G₂).edgeFinset = G₁.edgeFinset ∩ G₂.edgeFinset := by
  simp [edgeFinset]

@[simp]
theorem edgeFinset_sdiff [DecidableEq V] :
    (G₁ \ G₂).edgeFinset = G₁.edgeFinset \ G₂.edgeFinset := by simp [edgeFinset]

-- lemma disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂ := by
--   simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

-- lemma edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥ := by
--   rw [← edgeFinset_bot, edgeFinset_inj]

-- lemma edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
--   rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]

theorem edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet :=
  Set.toFinset_card _

@[simp]
theorem edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset :=
  Fintype.card_of_subtype G.edgeFinset fun _ => mem_edgeFinset

variable [Fintype V]

@[simp]
theorem edgeFinset_top [DecidableEq V] :
    (⊤ : MyGraph V).edgeFinset = ({e | ¬e.IsDiag} : Finset _) := by simp [← coe_inj]

/-- The complete graph on `n` vertices has `n.choose 2` edges. -/
theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : MyGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [Set.toFinset_card, edgeSet_top, Set.coe_setOf, ← Sym2.card_subtype_not_diag]

/-- Any graph on `n` vertices has at most `n.choose 2` edges. -/
theorem card_edgeFinset_le_card_choose_two : #G.edgeFinset ≤ (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

theorem edgeFinset_deleteEdges [DecidableEq V] [Fintype G.edgeSet] (s : Finset (Sym2 V))
    [Fintype (G.deleteEdges s).edgeSet] :
    (G.deleteEdges s).edgeFinset = G.edgeFinset \ s := by
  ext e
  simp [edgeSet_deleteEdges]

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

/-- `G.neighbors v` is the `Finset` version of `G.Adj v` in case `G` is
locally finite at `v`. -/
def neighborFinset : Finset V :=
  (G.neighborSet v).toFinset

theorem neighborFinset_def : G.neighborFinset v = (G.neighborSet v).toFinset :=
  rfl

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset

theorem not_mem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| not_mem_neighborFinset_self _ _

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| not_mem_neighborFinset_self _ _

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

theorem degree_eq_zero_iff_not_mem_support : G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v, Nat.pos_iff_ne_zero, not_ne_iff]


def finiteAtOfSubgraph {G G' : MyGraph V} [DecidableRel G.Adj] (h : G ≤ G') (v : G.verts)
    [Fintype (G'.neighborSet v)] : Fintype (G.neighborSet v) :=
  Set.fintypeSubset (G'.neighborSet v) (neighborSet_subset_of_subgraph h v)

instance (G : MyGraph V) [Fintype G.verts] (v : V) [DecidablePred (· ∈ G.neighborSet v)] :
    Fintype (G.neighborSet v) :=
  Set.fintypeSubset G.verts (neighborSet_subset_verts G v)


theorem degree_le' (G G' : MyGraph V) (h : G ≤ G') (v : V) [Fintype (G.neighborSet v)]
    [Fintype (G'.neighborSet v)] : G.degree v ≤ G'.degree v := by
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card (neighborSet_subset_of_subgraph h v)

theorem degree_eq_one_iff_unique_adj {G : MyGraph V} {v : V} [Fintype (G.neighborSet v)] :
    G.degree v = 1 ↔ ∃! w : V, G.Adj v w := by
  rw [← card_neighborFinset_eq_degree , Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]

-- theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
--     Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
--   classical
--     rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
--     simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v))]

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

-- theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : MyGraph V} [DecidableRel G.Adj]
--     {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
--   intro v
--   rw [degree_compl, h v]

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

-- theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
--     Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
--   simp only [neighborFinset, neighborSet_compl, Set.toFinset_diff, Set.toFinset_compl,
--     Set.toFinset_singleton]

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (⊤ : MyGraph V).degree v = Fintype.card V - 1 := by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v), card_univ]

theorem bot_degree (v : V) : (⊥ : MyGraph V).degree v = 0 := by
  simp_rw [degree, neighborFinset_eq_filter, not_bot_adj, filter_False]
  exact Finset.card_empty

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : MyGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
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
lemma minDegree_le_minDegree {H : MyGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) : G.minDegree ≤ H.minDegree := by
  by_cases hne : Nonempty V
  · apply le_minDegree_of_forall_le_degree
    exact fun v ↦ (G.minDegree_le_degree v).trans (G.degree_le' _  hle _)
  · rw [not_nonempty_iff] at hne
    simp

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  Option.getD (univ.image fun v => G.degree v).max 0

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  obtain ⟨t, ht⟩ := max_of_nonempty (univ_nonempty.image fun v => G.degree v)
  have ht₂ := mem_of_max ht
  simp only [mem_image, mem_univ, exists_prop_of_true] at ht₂
  rcases ht₂ with ⟨v, _, rfl⟩
  refine ⟨v, ?_⟩
  rw [maxDegree, ht]
  rfl

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree := by
  obtain ⟨t, ht : _ = _⟩ := Finset.max_of_mem (mem_image_of_mem (fun v => G.degree v) (mem_univ v))
  have := Finset.le_max_of_eq (mem_image_of_mem _ (mem_univ v)) ht
  rwa [maxDegree, ht]

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  by_cases hV : (univ : Finset V).Nonempty
  · haveI : Nonempty V := univ_nonempty_iff.mp hV
    obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
    rw [hv]
    apply h
  · rw [not_nonempty_iff_eq_empty] at hV
    rw [maxDegree, hV, image_empty]
    exact k.zero_le

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
theorem Adj.card_commonNeighbors_lt_degree {G : MyGraph V} [DecidableRel G.Adj] {v w : V}
    (h : G.Adj v w) : Fintype.card (G.commonNeighbors v w) < G.degree v := by
  classical
  rw [← Set.toFinset_card]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff]
  use w
  constructor
  · rw [Set.mem_toFinset]
    apply not_mem_commonNeighbors_right
  · rw [Finset.insert_subset_iff]
    constructor
    · simpa
    · rw [neighborFinset, Set.toFinset_subset_toFinset]
      exact G.commonNeighbors_subset_neighborSet_left _ _

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card ((⊤ : MyGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card, Set.toFinset_diff]
  rw [Finset.card_sdiff]
  · simp [Finset.card_univ, h]
  · simp only [Set.toFinset_subset_toFinset, Set.subset_univ]

end Finite

section Support

variable {s : Set V} [DecidablePred (· ∈ s)] [Fintype V] {G : MyGraph V} [DecidableRel G.Adj]

lemma edgeFinset_subset_sym2_of_support_subset (h : G.support ⊆ s) :
    G.edgeFinset ⊆ s.toFinset.sym2 := by
  simp_rw [subset_iff, Sym2.forall,
    mem_edgeFinset, mem_edgeSet, mk_mem_sym2_iff, Set.mem_toFinset]
  intro _ _ hadj
  exact ⟨h ⟨_, hadj⟩, h ⟨_, hadj.symm⟩⟩

instance : DecidablePred (· ∈ G.support) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | ∃ w, G.Adj v w })

variable [DecidableEq V]

instance fintypeEdgeSetInduce : Fintype (G.induce s).edgeSet := by
  rw [edgeSet_induce]
  apply Set.fintypeSubset G.edgeSet (fun x hx ↦ hx.1)

theorem edgeFinset_induce :
    (G.induce s).edgeFinset = G.edgeFinset ∩ s.toFinset.sym2 := by
  ext e; cases e; aesop

theorem edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    (G.induce s).edgeFinset = G.edgeFinset := by
  simp_rw [edgeFinset, edgeSet_induce_of_support_subset _ h]


/-- If the support of the simple graph `G` is a subset of the set `s`, then the induced subgraph of
`s` has the same number of edges as `G`. -/
theorem card_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    #(G.induce s).edgeFinset = #G.edgeFinset := by
  rw [edgeFinset_induce_of_support_subset h]

theorem card_edgeFinset_induce_support :
    #(G.induce G.support).edgeFinset = #G.edgeFinset :=
  card_edgeFinset_induce_of_support_subset subset_rfl


variable (G)
instance fintypeNeighborSetInduce {v : V} : Fintype ((G.induce s).neighborSet v) := by
  by_cases h : v ∈ s
  · rw [neighborSet_induce_of_mem _ h]
    apply Set.fintypeSubset (G.neighborSet v) (fun x hx ↦ hx.2)
  · rw [neighborSet_induce_of_not_mem _ h]
    exact Set.fintypeEmpty

theorem neighborFinset_induce {v : V} (h : v ∈ s) :
    (G.induce s).neighborFinset v = s.toFinset  ∩ G.neighborFinset v := by
  ext x
  simp [h]

theorem neighborFinset_induce_of_neighborSet_subset {v : V} (h : v ∈ s) (h1 : G.neighborSet v ⊆ s) :
    (G.induce s).neighborFinset v = G.neighborFinset v := by
  rw [ ← Set.toFinset_subset_toFinset, ← inter_eq_right, ← neighborFinset_def] at h1
  rw [neighborFinset_induce G h, h1 ]

/-- If the neighbor set of a vertex `v` is a subset of `s`, then the degree of the vertex in the
induced subgraph of `s` is the same as in `G`. -/
theorem degree_induce_of_neighborSet_subset {v : V} (h : v ∈ s) (h1 : G.neighborSet v ⊆ s) :
    (G.induce s).degree v = G.degree v := by
  simp_rw [← card_neighborFinset_eq_degree, G.neighborFinset_induce_of_neighborSet_subset h h1]

/-- If the support of the simple graph `G` is a subset of the set `s`, then the degree of vertices
in the induced subgraph of `s` are the same as in `G`. -/
theorem degree_induce_of_support_subset {v : V} (h : v ∈ s) (h1 : G.support ⊆ s)  :
    (G.induce s).degree v = G.degree v :=
  G.degree_induce_of_neighborSet_subset h <| (G.neighborSet_subset_support v).trans h1

@[simp]
theorem degree_induce_support {v : V} (h1 : v ∈ G.support) :
    (G.induce G.support).degree v = G.degree v :=
  G.degree_induce_of_support_subset h1 subset_rfl

end Support

end MyGraph

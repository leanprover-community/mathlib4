/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Sym.Card

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

@[expose] public section


open Finset Function

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V) {e : Sym2 V}

section EdgeFinset

variable {G₁ G₂ : SimpleGraph V} [Fintype G.edgeSet] [Fintype G₁.edgeSet] [Fintype G₂.edgeSet]

/-- The `edgeSet` of the graph as a `Finset`. -/
def edgeFinset : Finset (Sym2 V) :=
  Set.toFinset G.edgeSet

@[simp, norm_cast]
theorem coe_edgeFinset : (G.edgeFinset : Set (Sym2 V)) = G.edgeSet :=
  Set.coe_toFinset _

variable {G}

@[simp]
theorem mem_edgeFinset : e ∈ G.edgeFinset ↔ e ∈ G.edgeSet :=
  Set.mem_toFinset

theorem not_isDiag_of_mem_edgeFinset : e ∈ G.edgeFinset → ¬e.IsDiag :=
  not_isDiag_of_mem_edgeSet _ ∘ mem_edgeFinset.1

/-- Mapping an edge to a finite set produces a finset of size `2`. -/
theorem card_toFinset_mem_edgeFinset [DecidableEq V] (e : G.edgeFinset) :
    (e : Sym2 V).toFinset.card = 2 :=
  Sym2.card_toFinset_of_not_isDiag e.val (G.not_isDiag_of_mem_edgeFinset e.prop)

@[simp]
theorem edgeFinset_inj : G₁.edgeFinset = G₂.edgeFinset ↔ G₁ = G₂ := by simp [edgeFinset]

@[simp]
theorem edgeFinset_subset_edgeFinset : G₁.edgeFinset ⊆ G₂.edgeFinset ↔ G₁ ≤ G₂ := by
  simp [edgeFinset]

@[simp]
theorem edgeFinset_ssubset_edgeFinset : G₁.edgeFinset ⊂ G₂.edgeFinset ↔ G₁ < G₂ := by
  simp [edgeFinset]

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

@[simp]
lemma disjoint_edgeFinset : Disjoint G₁.edgeFinset G₂.edgeFinset ↔ Disjoint G₁ G₂ := by
  simp_rw [← Finset.disjoint_coe, coe_edgeFinset, disjoint_edgeSet]

@[simp]
lemma edgeFinset_eq_empty : G.edgeFinset = ∅ ↔ G = ⊥ := by
  rw [← edgeFinset_bot, edgeFinset_inj]

@[simp]
lemma edgeFinset_nonempty : G.edgeFinset.Nonempty ↔ G ≠ ⊥ := by
  rw [Finset.nonempty_iff_ne_empty, edgeFinset_eq_empty.ne]

theorem edgeFinset_card : #G.edgeFinset = Fintype.card G.edgeSet :=
  Set.toFinset_card _

theorem card_edgeSet : Fintype.card G.edgeSet = #G.edgeFinset :=
  .symm <| Set.toFinset_card _

theorem edgeSet_univ_card : #(univ : Finset G.edgeSet) = #G.edgeFinset := by
  simp [card_edgeSet]

variable [Fintype V]

@[simp]
theorem edgeFinset_top [DecidableEq V] :
    (⊤ : SimpleGraph V).edgeFinset = Sym2.diagSetᶜ.toFinset := by simp [← coe_inj]

/-- The complete graph on `n` vertices has `n.choose 2` edges. -/
theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [edgeFinset, Set.toFinset_card, edgeSet_top, ← Sym2.card_diagSet_compl]

/-- Any graph on `n` vertices has at most `n.choose 2` edges. -/
theorem card_edgeFinset_le_card_choose_two : #G.edgeFinset ≤ (Fintype.card V).choose 2 := by
  classical
  rw [← card_edgeFinset_top_eq_card_choose_two]
  exact card_le_card (edgeFinset_mono le_top)

end EdgeFinset

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

@[simp, norm_cast]
theorem coe_neighborFinset : (G.neighborFinset v : Set V) = G.neighborSet v :=
  Set.coe_toFinset _

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset

theorem notMem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| notMem_neighborFinset_self _ _

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| notMem_neighborFinset_self _ _

@[simp] lemma neighborFinset_eq_empty : G.neighborFinset v = ∅ ↔ G.IsIsolated v := by
  simp [neighborFinset, IsIsolated, Set.ext_iff]

@[simp] lemma neighborFinset_nonempty : (G.neighborFinset v).Nonempty ↔ ¬ G.IsIsolated v := by
  simp [nonempty_iff_ne_empty]

protected alias ⟨IsIsolated.of_neighborFinset_eq_empty, IsIsolated.neighborFinset_eq_empty⟩
    := neighborFinset_eq_empty

attribute [simp] IsIsolated.neighborFinset_eq_empty

/-- `G.degree v` is the number of vertices adjacent to `v`. -/
def degree : ℕ := #(G.neighborFinset v)

@[simp]
theorem card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v := rfl

theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  (Set.toFinset_card _).symm

lemma degree_eq_zero : G.degree v = 0 ↔ G.IsIsolated v := by simp [← card_neighborFinset_eq_degree]
lemma degree_pos : 0 < G.degree v ↔ ¬ G.IsIsolated v := by simp [← card_neighborFinset_eq_degree]

protected alias ⟨IsIsolated.of_degree_eq_zero, IsIsolated.degree_eq_zero⟩ := degree_eq_zero

attribute [simp] IsIsolated.degree_eq_zero

theorem degree_pos_iff_exists_adj : 0 < G.degree v ↔ ∃ w, G.Adj v w := by
  simp only [degree, card_pos, Finset.Nonempty, mem_neighborFinset]

variable {G v} in
theorem degree_pos_iff_nonempty : 0 < G.degree v ↔ (G.neighborSet v).Nonempty :=
  G.degree_pos_iff_exists_adj v

variable {G v} in
theorem Adj.degree_pos_left {w : V} (h : G.Adj v w) : 0 < G.degree v :=
  G.degree_pos_iff_nonempty.mpr ⟨_, h⟩

variable {G v} in
theorem Adj.degree_pos_right {w : V} (h : G.Adj w v) : 0 < G.degree v :=
  h.symm.degree_pos_left

theorem degree_pos_iff_mem_support : 0 < G.degree v ↔ v ∈ G.support := by
  rw [G.degree_pos_iff_exists_adj v, mem_support]

theorem degree_eq_zero_iff_notMem_support : G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v, Nat.pos_iff_ne_zero, not_ne_iff]

theorem degree_eq_zero_of_subsingleton {G : SimpleGraph V} (v : V) [Fintype (G.neighborSet v)]
    [Subsingleton V] : G.degree v = 0 := by
  simp

theorem nontrivial_of_degree_ne_zero {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)]
    (h : G.degree v ≠ 0) : Nontrivial V :=
  nontrivial_of_not_isIsolated <| G.degree_eq_zero v |>.not.mp h

theorem degree_eq_one_iff_existsUnique_adj {G : SimpleGraph V} {v : V} [Fintype (G.neighborSet v)] :
    G.degree v = 1 ↔ ∃! w : V, G.Adj v w := by
  rw [degree, Finset.card_eq_one, Finset.singleton_iff_unique_mem]
  simp only [mem_neighborFinset]

theorem degree_compl [Fintype (Gᶜ.neighborSet v)] [Fintype V] :
    Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
    rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
    simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v)),
      card_neighborSet_eq_degree]

instance incidenceSetFintype : Fintype (G.incidenceSet v) :=
  .ofBijective (α := G.neighborSet v) (⟨_, G.mem_incidence_iff_neighbor.mpr ·.prop⟩) <| by
    classical exact G.incidenceSetEquivNeighborSet v |>.symm.bijective

/-- This is the `Finset` version of `incidenceSet`. -/
def incidenceFinset [DecidableEq V] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset

theorem card_incidenceSet_eq_degree : Fintype.card (G.incidenceSet v) = G.degree v := by
  classical
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v), card_neighborSet_eq_degree]

@[simp, norm_cast]
theorem coe_incidenceFinset [DecidableEq V] :
    (G.incidenceFinset v : Set (Sym2 V)) = G.incidenceSet v := by
  simp [incidenceFinset]

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
  ext ⟨⟨⟩⟩
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

theorem degree_lt_card_verts [Fintype V] [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V :=
  Finset.card_lt_univ_of_notMem <| G.notMem_neighborFinset_self v

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

/-- The empty graph is regular of any degree `d` -/
@[simp]
theorem IsRegularOfDegree.of_isEmpty [IsEmpty V] {d : ℕ} : G.IsRegularOfDegree d :=
  IsEmpty.elim ‹_›

theorem IsRegularOfDegree.compl [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {k : ℕ} (h : G.IsRegularOfDegree k) : Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  rw [degree_compl, h v]

end LocallyFinite

section Finite

variable [Fintype V]

/-- `Fintype` for `neighborSet` -/
@[deprecated inferInstance (since := "2026-04-29")]
abbrev neighborSetFintype [DecidableRel G.Adj] (v : V) : Fintype (G.neighborSet v) :=
  inferInstance

theorem neighborFinset_eq_filter {v : V} [DecidableRel G.Adj] :
    G.neighborFinset v = ({w | G.Adj v w} : Finset _) := by ext; simp

theorem neighborFinset_compl [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_sdiff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
theorem complete_graph_degree [DecidableEq V] (v : V) :
    (completeGraph V).degree v = Fintype.card V - 1 := by
  simp_rw [degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v), card_univ]

theorem bot_degree (v : V) : (⊥ : SimpleGraph V).degree v = 0 := by
  simp

theorem IsRegularOfDegree.top [DecidableEq V] :
    (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  simp [IsRegularOfDegree]

@[simp]
theorem IsRegularOfDegree.bot : (⊥ : SimpleGraph V).IsRegularOfDegree 0 :=
  bot_degree

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegree_le_degree`
and `le_minDegree_of_forall_le_degree`. -/
def minDegree [DecidableRel G.Adj] : ℕ :=
  WithTop.untopD 0 (univ.image fun v => G.degree v).min

/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_minimal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.minDegree = G.degree v := by
  grind [minDegree, WithTop.untopD_coe, min_mem_image_coe <| univ_nonempty.image (G.degree ·)]

/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree [DecidableRel G.Adj] (v : V) : G.minDegree ≤ G.degree v :=
  WithTop.untopD_le <| Finset.min_le <| mem_image_of_mem (G.degree ·) <| mem_univ v

/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
theorem le_minDegree_of_forall_le_degree [DecidableRel G.Adj] [Nonempty V] (k : ℕ)
    (h : ∀ v, k ≤ G.degree v) : k ≤ G.minDegree := by
  rcases G.exists_minimal_degree_vertex with ⟨v, hv⟩
  rw [hv]
  apply h

@[simp]
lemma minDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.minDegree = 0 := by
  cases isEmpty_or_nonempty V <;>
    simp [minDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias minDegree_of_isEmpty := minDegree_of_subsingleton

variable {G} in
/-- If `G` is a subgraph of `H` then `G.minDegree ≤ H.minDegree`. -/
@[gcongr]
lemma minDegree_le_minDegree {H : SimpleGraph V} [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hle : G ≤ H) : G.minDegree ≤ H.minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  · apply le_minDegree_of_forall_le_degree
    exact fun v ↦ (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)

/-- In a nonempty graph, the minimal degree is less than the number of vertices. -/
theorem minDegree_lt_card [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree < Fintype.card V := by
  have ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  rw [hv]
  apply degree_lt_card_verts

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
def maxDegree [DecidableRel G.Adj] : ℕ :=
  WithBot.unbotD 0 (univ.image fun v => G.degree v).max

/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_maximal_degree_vertex [DecidableRel G.Adj] [Nonempty V] :
    ∃ v, G.maxDegree = G.degree v := by
  grind [maxDegree, WithBot.unbotD_coe, max_mem_image_coe <| univ_nonempty.image (G.degree ·)]

/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [DecidableRel G.Adj] (v : V) : G.degree v ≤ G.maxDegree :=
  WithBot.le_unbotD <| Finset.le_max <| mem_image_of_mem (G.degree ·) <| mem_univ v

@[simp]
lemma maxDegree_of_subsingleton [DecidableRel G.Adj] [Subsingleton V] : G.maxDegree = 0 := by
  cases isEmpty_or_nonempty V <;>
    simp [maxDegree, Finset.image_const]

@[deprecated (since := "2026-06-15")] alias maxDegree_of_isEmpty := maxDegree_of_subsingleton

/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le [DecidableRel G.Adj] (k : ℕ) (h : ∀ v, G.degree v ≤ k) :
    G.maxDegree ≤ k := by
  cases isEmpty_or_nonempty V
  · simp
  · obtain ⟨_, hv⟩ := G.exists_maximal_degree_vertex
    exact hv ▸ h _

theorem IsRegularOfDegree.maxDegree_eq [Nonempty V] [DecidableRel G.Adj] {d : ℕ}
    (h : G.IsRegularOfDegree d) : G.maxDegree = d := by
  simp [maxDegree, h.degree_eq, Finset.image_const]

@[simp]
lemma maxDegree_bot_eq_zero : (⊥ : SimpleGraph V).maxDegree = 0 :=
  Nat.le_zero.1 <| maxDegree_le_of_forall_degree_le _ _ (by simp)

variable {G} in
@[simp]
theorem maxDegree_eq_zero_iff [DecidableRel G.Adj] : G.maxDegree = 0 ↔ G = ⊥ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [eq_bot_iff_isIsolated]
    intro v
    grind [degree_eq_zero, G.degree_le_maxDegree v]
  · convert maxDegree_bot_eq_zero
    assumption

@[simp]
lemma maxDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).maxDegree = Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.maxDegree_eq

@[simp]
lemma minDegree_le_maxDegree [DecidableRel G.Adj] : G.minDegree ≤ G.maxDegree := by
  by_cases! he : IsEmpty V
  · simp
  · exact he.elim fun v ↦ (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)

theorem IsRegularOfDegree.minDegree_eq [Nonempty V] [DecidableRel G.Adj] {d : ℕ}
    (h : G.IsRegularOfDegree d) : G.minDegree = d := by
  simp [minDegree, h.degree_eq, Finset.image_const]

@[simp]
lemma minDegree_bot_eq_zero : (⊥ : SimpleGraph V).minDegree = 0 :=
  Nat.le_zero.1 <| (minDegree_le_maxDegree _).trans (by simp)

variable {G} in
theorem minDegree_eq_zero_iff [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree = 0 ↔ ∃ v, G.IsIsolated v := by
  refine ⟨fun h ↦ ?_, fun ⟨v, hv⟩ ↦ ?_⟩
  · grind [G.exists_minimal_degree_vertex, degree_eq_zero]
  · grind [G.minDegree_le_degree v, degree_eq_zero]

variable {G} in
theorem minDegree_eq_zero_iff_support_ne [DecidableRel G.Adj] [Nonempty V] :
    G.minDegree = 0 ↔ G.support ≠ .univ := by
  simp [Set.ne_univ_iff_exists_notMem, minDegree_eq_zero_iff]

@[simp]
lemma minDegree_top [DecidableEq V] : (⊤ : SimpleGraph V).minDegree = Fintype.card V - 1 := by
  cases isEmpty_or_nonempty V
  · simp
  exact IsRegularOfDegree.top.minDegree_eq

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
  refine Finset.card_lt_card <| Finset.ssubset_iff.mpr ⟨w, ?_, ?_⟩
  · rw [Set.mem_toFinset]
    apply notMem_commonNeighbors_right
  · simpa [Finset.insert_subset_iff, G.commonNeighbors_subset_neighborSet_left v w]

theorem card_commonNeighbors_top [DecidableEq V] {v w : V} (h : v ≠ w) :
    Fintype.card (commonNeighbors ⊤ v w) = Fintype.card V - 2 := by
  simp [commonNeighbors_top_eq, ← Set.toFinset_card, Finset.card_sdiff, h]

@[simp] lemma insert_neighborFinset_eq_univ [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    insert v (G.neighborFinset v) = univ ↔ G.IsUniversal v := by
  simp only [Finset.ext_iff, mem_insert, mem_neighborFinset, IsUniversal]
  grind

@[simp] lemma neighborFinset_eq_erase_univ [DecidableEq V] [DecidableRel G.Adj] (v : V) :
    G.neighborFinset v = univ.erase v ↔ G.IsUniversal v := by
  grind [insert_neighborFinset_eq_univ, notMem_neighborFinset_self]

@[simp]
lemma degree_eq_card_sub_one [DecidableRel G.Adj] (v : V) :
    G.degree v = Fintype.card V - 1 ↔ G.IsUniversal v := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [← G.insert_neighborFinset_eq_univ v, ← Finset.card_eq_iff_eq_univ]
    simp [h, Nat.sub_add_cancel <| Fintype.card_pos_iff.mpr ⟨v⟩]
  · simp [← card_neighborFinset_eq_degree, (G.neighborFinset_eq_erase_univ v).mpr h]

lemma degree_lt_card_sub_one [DecidableRel G.Adj] (v : V) :
    G.degree v < Fintype.card V - 1 ↔ ¬ G.IsUniversal v := by
  grind [degree_eq_card_sub_one, Nat.le_sub_one_of_lt <| G.degree_lt_card_verts v]

end Finite

namespace Iso

variable {G} {W : Type*} {G' : SimpleGraph W}

theorem card_edgeFinset_eq (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    #G.edgeFinset = #G'.edgeFinset := by
  apply Finset.card_eq_of_equiv
  simpa using f.mapEdgeSet

@[simp] theorem degree_eq (f : G ≃g G') (x : V)
    [Fintype ↑(G.neighborSet x)] [Fintype ↑(G'.neighborSet (f x))] :
    G'.degree (f x) = G.degree x := by
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree,
    ← Fintype.card_congr (mapNeighborSet f x).symm]

variable [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel G'.Adj]

theorem minDegree_eq (f : G ≃g G') : G.minDegree = G'.minDegree := by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [minDegree, minDegree, ← this, ← image_image, Finset.image_univ_of_surjective f.surjective]

theorem maxDegree_eq (f : G ≃g G') : G.maxDegree = G'.maxDegree := by
  classical
  have : (G'.degree ·) ∘ f = (G.degree ·) := funext (f.degree_eq ·)
  rw [maxDegree, maxDegree, ← this, ← image_image, Finset.image_univ_of_surjective f.surjective]

end Iso

section Support

variable {s : Set V} [DecidablePred (· ∈ s)] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma edgeFinset_subset_sym2_of_support_subset (h : G.support ⊆ s) :
    G.edgeFinset ⊆ s.toFinset.sym2 := by
  rw [← coe_subset, coe_sym2, edgeFinset, Set.coe_toFinset, Set.coe_toFinset]
  exact edgeSet_subset_sym2_iff.mpr h

instance : DecidablePred (· ∈ G.support) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | ∃ w, G.Adj v w })

theorem map_edgeFinset_induce [DecidableEq V] :
    (G.induce s).edgeFinset.map (Embedding.subtype (· ∈ s)).sym2Map
      = G.edgeFinset ∩ s.toFinset.sym2 := by
  aesop (add simp [Finset.ext_iff, Sym2.exists, Sym2.forall, adj_comm])

theorem map_edgeFinset_induce_of_support_subset (h : G.support ⊆ s) :
    (G.induce s).edgeFinset.map (Embedding.subtype (· ∈ s)).sym2Map = G.edgeFinset := by
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
    ((G.induce s).neighborFinset v).map (.subtype (· ∈ s)) = G.neighborFinset v := by
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

theorem le_minDegree_induce_of_support_subset (h : G.support ⊆ s) :
    G.minDegree ≤ (G.induce s).minDegree := by
  cases isEmpty_or_nonempty V
  · simp
  rcases s.eq_empty_or_nonempty with (rfl | hs)
  · simp [minDegree_eq_zero_iff_support_ne, Set.subset_empty_iff.mp h, Set.empty_ne_univ]
  have := hs.to_subtype
  refine le_minDegree_of_forall_le_degree _ _ fun v ↦ ?_
  grw [G.minDegree_le_degree v, degree_induce_of_neighborSet_subset]
  grw [neighborSet_subset_support, h]

end Support

section Map

variable [Fintype V] {W : Type*} [Fintype W] [DecidableEq W]

@[simp]
theorem edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    (G.map f).edgeFinset = G.edgeFinset.map f.sym2Map := by
  rw [← Finset.coe_inj]
  push_cast
  exact G.edgeSet_map f

theorem card_edgeFinset_map (f : V ↪ W) (G : SimpleGraph V) [DecidableRel G.Adj] :
    #(G.map f).edgeFinset = #G.edgeFinset := by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

end Map

end SimpleGraph

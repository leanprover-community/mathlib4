/-
Copyright (c) 2020 Aaron Anderson, Jalex Stark, Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller, Alena Gusakov
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
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
    (⊤ : SimpleGraph V).edgeFinset = Sym2.diagSetᶜ.toFinset := by simp [← coe_inj]

/-- The complete graph on `n` vertices has `n.choose 2` edges. -/
theorem card_edgeFinset_top_eq_card_choose_two [DecidableEq V] :
    #(⊤ : SimpleGraph V).edgeFinset = (Fintype.card V).choose 2 := by
  simp_rw [Set.toFinset_card, edgeSet_top, ← Sym2.card_diagSet_compl]

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

@[simp]
theorem mem_neighborFinset (w : V) : w ∈ G.neighborFinset v ↔ G.Adj v w :=
  Set.mem_toFinset

theorem notMem_neighborFinset_self : v ∉ G.neighborFinset v := by simp

theorem neighborFinset_disjoint_singleton : Disjoint (G.neighborFinset v) {v} :=
  Finset.disjoint_singleton_right.mpr <| notMem_neighborFinset_self _ _

theorem singleton_disjoint_neighborFinset : Disjoint {v} (G.neighborFinset v) :=
  Finset.disjoint_singleton_left.mpr <| notMem_neighborFinset_self _ _

/-- `G.edegree v` is the number of vertices adjacent to `v`, or `⊤` if there are infinitely many -/
noncomputable def edegree : ℕ∞ :=
  G.neighborSet v |>.encard

/-- `G.degree v` is the number of vertices adjacent to `v`, or `0` if there are infinitely many -/
noncomputable def degree : ℕ :=
  G.neighborSet v |>.ncard

@[simp]
theorem card_neighborFinset_eq_degree : #(G.neighborFinset v) = G.degree v :=
  Set.ncard_eq_toFinset_card' _ |>.symm

@[simp]
theorem card_neighborSet_eq_degree : Fintype.card (G.neighborSet v) = G.degree v :=
  Set.ncard_eq_card _ |>.symm

omit [Fintype <| G.neighborSet v] in
theorem degree_pos_iff_exists_adj [Finite <| G.neighborSet v] : 0 < G.degree v ↔ ∃ w, G.Adj v w :=
  Set.ncard_pos

omit [Fintype <| G.neighborSet v] in
theorem degree_pos_iff_mem_support [Finite <| G.neighborSet v] :
    0 < G.degree v ↔ v ∈ G.support := by
  rw [G.degree_pos_iff_exists_adj v, mem_support]

omit [Fintype <| G.neighborSet v] in
theorem degree_eq_zero_iff_notMem_support [Finite <| G.neighborSet v] :
    G.degree v = 0 ↔ v ∉ G.support := by
  rw [← G.degree_pos_iff_mem_support v, Nat.pos_iff_ne_zero, not_ne_iff]

variable {G} in
@[simp]
theorem degree_eq_zero_of_subsingleton (v : V) [Subsingleton V] : G.degree v = 0 := by
  have := G.degree_pos_iff_exists_adj v
  simp_all [subsingleton_iff_forall_eq v]

omit [Fintype <| G.neighborSet v] in
variable {G} in
theorem degree_eq_one_iff_existsUnique_adj {v : V} : G.degree v = 1 ↔ ∃! w : V, G.Adj v w := by
  rw [degree, Set.ncard_eq_one, Set.singleton_iff_unique_mem]
  rfl

variable {G} in
theorem nontrivial_of_degree_ne_zero {v : V} (h : G.degree v ≠ 0) : Nontrivial V := by
  by_contra!
  simp_all [degree_eq_zero_of_subsingleton]

omit [Fintype <| G.neighborSet v] in
theorem degree_compl [Fintype V] : Gᶜ.degree v = Fintype.card V - 1 - G.degree v := by
  classical
  have := Fintype.ofFinite <| G.neighborSet v
  have := Fintype.ofFinite <| Gᶜ.neighborSet v
  rw [← card_neighborSet_union_compl_neighborSet G v, Set.toFinset_union]
  simp [card_union_of_disjoint (Set.disjoint_toFinset.mpr (compl_neighborSet_disjoint G v))]

instance incidenceSetFintype [DecidableEq V] : Fintype (G.incidenceSet v) :=
  Fintype.ofEquiv (G.neighborSet v) (G.incidenceSetEquivNeighborSet v).symm

omit [Fintype <| G.neighborSet v] in
/-- This is the `Finset` version of `incidenceSet`. -/
def incidenceFinset [Fintype <| G.incidenceSet v] : Finset (Sym2 V) :=
  (G.incidenceSet v).toFinset

omit [Fintype <| G.neighborSet v] in
@[simp]
theorem card_incidenceSet_eq_degree [Fintype <| G.incidenceSet v] :
    Fintype.card (G.incidenceSet v) = G.degree v := by
  classical
  have := Fintype.ofEquiv _ <| G.incidenceSetEquivNeighborSet v
  rw [Fintype.card_congr (G.incidenceSetEquivNeighborSet v)]
  simp

omit [Fintype <| G.neighborSet v] in
@[simp]
theorem card_incidenceFinset_eq_degree [Fintype <| G.incidenceSet v] :
    #(G.incidenceFinset v) = G.degree v := by
  rw [← G.card_incidenceSet_eq_degree]
  apply Set.toFinset_card

omit [Fintype <| G.neighborSet v] in
@[simp]
theorem mem_incidenceFinset [Fintype <| G.incidenceSet v] (e : Sym2 V) :
    e ∈ G.incidenceFinset v ↔ e ∈ G.incidenceSet v :=
  Set.mem_toFinset

omit [Fintype <| G.neighborSet v] in
theorem incidenceFinset_eq_filter [DecidableEq V] [Fintype <| G.incidenceSet v]
    [Fintype G.edgeSet] : G.incidenceFinset v = {e ∈ G.edgeFinset | v ∈ e} := by
  ext e
  induction e
  simp [mk'_mem_incidenceSet_iff]

omit [Fintype <| G.neighborSet v] in
theorem incidenceFinset_subset [Fintype <| G.incidenceSet v] [Fintype G.edgeSet] :
    G.incidenceFinset v ⊆ G.edgeFinset :=
  Set.toFinset_subset_toFinset.mpr (G.incidenceSet_subset v)

omit [Fintype <| G.neighborSet v] in
/-- The degree of a vertex is at most the number of edges. -/
theorem degree_le_card_edgeFinset [Fintype G.edgeSet] : G.degree v ≤ #G.edgeFinset := by
  have := @Fintype.ofFinite _ <| Finite.Set.subset _ <| G.incidenceSet_subset v
  exact G.card_incidenceFinset_eq_degree v ▸ card_le_card (G.incidenceFinset_subset v)

variable {G v}

omit [Fintype <| G.neighborSet v] in
/-- If `G ≤ H` then `G.degree v ≤ H.degree v` for any vertex `v`. -/
lemma degree_le_of_le {H : SimpleGraph V} [Finite <| H.neighborSet v] (hle : G ≤ H) :
    G.degree v ≤ H.degree v := by
  have := Fintype.ofFinite <| H.neighborSet v
  have := (Set.toFinite _ |>.subset <| neighborSet_subset hle v).fintype
  simp_rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card fun v hv => hle hv

end FiniteAt

section LocallyFinite

/-- A graph is locally finite if every vertex has a finite neighbor set. -/
abbrev LocallyFinite :=
  ∀ v : V, Fintype (G.neighborSet v)

/-- A simple graph is regular of degree `d` if every vertex has degree `d`. -/
def IsRegularOfDegree (d : ℕ) : Prop :=
  ∀ v : V, G.edegree v = d

variable {G}

theorem IsRegularOfDegree.degree_eq {d : ℕ} (h : G.IsRegularOfDegree d) (v : V) : G.degree v = d :=
  congrArg _ <| h v

theorem IsRegularOfDegree.compl [Fintype V] {k : ℕ} (h : G.IsRegularOfDegree k) :
    Gᶜ.IsRegularOfDegree (Fintype.card V - 1 - k) := by
  intro v
  have : Gᶜ.degree v = Gᶜ.edegree v := ENat.coe_toNat <| Set.encard_ne_top_iff.mpr <| Set.toFinite _
  rw [← this, degree_compl, h.degree_eq]

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

theorem neighborFinset_compl [DecidableEq V] (v : V) [Fintype <| G.neighborSet v]
    [Fintype <| Gᶜ.neighborSet v] : Gᶜ.neighborFinset v = (G.neighborFinset v)ᶜ \ {v} := by
  classical
  simp only [neighborFinset, neighborSet_compl, Set.toFinset_diff, Set.toFinset_compl,
    Set.toFinset_singleton]

@[simp]
theorem complete_graph_degree (v : V) : degree ⊤ v = Fintype.card V - 1 := by
  classical
  simp_rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, top_adj, filter_ne]
  rw [card_erase_of_mem (mem_univ v), card_univ]

omit [Fintype V] in
@[simp]
theorem bot_degree (v : V) : degree ⊥ v = 0 := by
  simp [degree, neighborSet]

theorem IsRegularOfDegree.top : (⊤ : SimpleGraph V).IsRegularOfDegree (Fintype.card V - 1) := by
  intro v
  have : degree ⊤ v = edegree ⊤ v := ENat.coe_toNat <| Set.encard_ne_top_iff.mpr <| Set.toFinite _
  simp [← this]

theorem IsRegularOfDegree.bot : (⊥ : SimpleGraph V).IsRegularOfDegree 0 := by
  intro v
  have : degree ⊥ v = edegree ⊥ v := ENat.coe_toNat <| Set.encard_ne_top_iff.mpr <| Set.toFinite _
  simp [← this]

/-- The minimum extended degree of all vertices (and `⊤` if there are no vertices) -/
noncomputable def eminDegree : ℕ∞ :=
  ⨅ v, G.edegree v

/-- The minimum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_minimal_degree_vertex`, `minDegree_le_degree`
and `le_minDegree_of_forall_le_degree`. -/
noncomputable def minDegree : ℕ :=
  G.eminDegree.toNat

omit [Fintype V] in
/-- There exists a vertex of minimal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_minimal_degree_vertex [Nonempty V] : ∃ v, G.minDegree = G.degree v := by
  have ⟨v, hv⟩ := ciInf_mem G.edegree
  exact ⟨v, congrArg _ hv.symm⟩

omit [Fintype V] in
/-- The minimum degree in the graph is at most the degree of any particular vertex. -/
theorem minDegree_le_degree (v : V) [Finite <| G.neighborSet v] : G.minDegree ≤ G.degree v :=
  ENat.toNat_le_toNat (iInf_le ..) (Set.encard_ne_top_iff.mpr ‹_›)

omit [Fintype V] in
/-- In a nonempty graph, if `k` is at most the degree of every vertex, it is at most the minimum
degree. Note the assumption that the graph is nonempty is necessary as long as `G.minDegree` is
defined to be a natural. -/
theorem le_minDegree_of_forall_le_degree [Nonempty V] (k : ℕ) (h : ∀ v, k ≤ G.degree v) :
    k ≤ G.minDegree := by
  have ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  exact hv ▸ h v

omit [Fintype V] in
/-- If there are no vertices then the `minDegree` is zero. -/
@[simp]
lemma minDegree_of_isEmpty [IsEmpty V] : G.minDegree = 0 :=
  ENat.toNat_eq_zero.mpr <| .inr <| iInf_of_empty G.edegree

omit [Fintype V] in
/-- If `G` is a subgraph of `H` then `G.minDegree ≤ H.minDegree`. -/
lemma minDegree_le_minDegree [Finite V] {G H : SimpleGraph V} (hle : G ≤ H) :
    G.minDegree ≤ H.minDegree := by
  by_cases! hne : Nonempty V
  · apply le_minDegree_of_forall_le_degree
    exact fun v ↦ (G.minDegree_le_degree v).trans (G.degree_le_of_le hle)
  · simp

/-- In a nonempty graph, the minimal degree is less than the number of vertices. -/
theorem minDegree_lt_card [Nonempty V] : G.minDegree < Fintype.card V := by
  classical
  obtain ⟨v, hδ⟩ := G.exists_minimal_degree_vertex
  rw [hδ, ← card_neighborFinset_eq_degree, ← card_univ]
  have h : v ∉ G.neighborFinset v :=
    (G.mem_neighborFinset v v).not.mpr (G.loopless v)
  contrapose! h
  rw [eq_of_subset_of_card_le (subset_univ _) h]
  exact mem_univ v

/-- The maximum extended degree of all vertices (and `0` if there are no vertices) -/
noncomputable def emaxDegree : ℕ∞ :=
  ⨆ v, G.edegree v

/-- The maximum degree of all vertices (and `0` if there are no vertices).
The key properties of this are given in `exists_maximal_degree_vertex`, `degree_le_maxDegree`
and `maxDegree_le_of_forall_degree_le`. -/
noncomputable def maxDegree : ℕ :=
  G.emaxDegree.toNat

omit [Fintype V] in
/-- There exists a vertex of maximal degree. Note the assumption of being nonempty is necessary, as
the lemma implies there exists a vertex. -/
theorem exists_maximal_degree_vertex [Nonempty V] [Finite V] : ∃ v, G.maxDegree = G.degree v := by
  have ⟨v, hv⟩ := Set.range_nonempty G.edegree |>.csSup_mem <| Set.finite_range _
  refine ⟨v, congrArg _ hv.symm⟩

omit [Fintype V] in
/-- The maximum degree in the graph is at least the degree of any particular vertex. -/
theorem degree_le_maxDegree [Finite V] (v : V) : G.degree v ≤ G.maxDegree := by
  refine ENat.toNat_le_toNat (le_iSup G.edegree v) ?_
  exact iSup_ne_top fun _ ↦ Set.encard_ne_top_iff.mpr <| Set.toFinite _

omit [Fintype V] in
@[simp]
lemma maxDegree_of_isEmpty [IsEmpty V] : G.maxDegree = 0 :=
  ENat.toNat_eq_zero.mpr <| .inl <| iSup_of_empty G.edegree

omit [Fintype V] in
/-- In a graph, if `k` is at least the degree of every vertex, then it is at least the maximum
degree. -/
theorem maxDegree_le_of_forall_degree_le (k : ℕ) (h : ∀ v, G.degree v ≤ k) : G.maxDegree ≤ k := by
  by_cases! htop : ∃ v, G.edegree v = ⊤
  · have ⟨v, hv⟩ := htop
    exact top_unique (hv ▸ le_iSup G.edegree v) ▸ ENat.toNat_top |>.trans_le <| by simp
  exact ENat.toNat_le_of_le_coe <| iSup_le ((WithTop.untopD_le_iff <| htop _).mp <| h ·)

omit [Fintype V] in
@[simp]
lemma maxDegree_bot_eq_zero : (⊥ : SimpleGraph V).maxDegree = 0 :=
  Nat.le_zero.1 <| maxDegree_le_of_forall_degree_le _ _ (by simp)

omit [Fintype V] in
@[simp]
lemma minDegree_le_maxDegree [Finite V] : G.minDegree ≤ G.maxDegree := by
  by_cases! he : IsEmpty V
  · simp
  · exact he.elim fun v ↦ (minDegree_le_degree _ v).trans (degree_le_maxDegree _ v)

omit [Fintype V] in
@[simp]
lemma minDegree_bot_eq_zero : (⊥ : SimpleGraph V).minDegree = 0 := by
  cases isEmpty_or_nonempty V
  · exact minDegree_of_isEmpty _
  have ⟨v, hv⟩ := (⊥ : SimpleGraph V).exists_minimal_degree_vertex
  exact hv ▸ bot_degree v

theorem degree_lt_card_verts (v : V) : G.degree v < Fintype.card V := by
  rw [Fintype.card_eq_nat_card]
  exact Set.ncard_lt_card <| Set.ne_univ_iff_exists_notMem _ |>.mpr ⟨v, G.notMem_neighborSet_self⟩

/--
The maximum degree of a nonempty graph is less than the number of vertices. Note that the assumption
that `V` is nonempty is necessary, as otherwise this would assert the existence of a
natural number less than zero. -/
theorem maxDegree_lt_card_verts [Nonempty V] : G.maxDegree < Fintype.card V := by
  have ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  exact hv ▸ G.degree_lt_card_verts v

omit [Fintype V] in
theorem card_commonNeighbors_le_degree_left (v w : V) [Fintype <| G.commonNeighbors v w]
    [Finite <| G.neighborSet v] : Fintype.card (G.commonNeighbors v w) ≤ G.degree v := by
  have := Fintype.ofFinite <| G.neighborSet v
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_left

omit [Fintype V] in
theorem card_commonNeighbors_le_degree_right (v w : V) [Fintype <| G.commonNeighbors v w]
    [Finite <| G.neighborSet w] : Fintype.card (G.commonNeighbors v w) ≤ G.degree w := by
  have := Fintype.ofFinite <| G.neighborSet w
  rw [← card_neighborSet_eq_degree]
  exact Set.card_le_card Set.inter_subset_right

theorem card_commonNeighbors_lt_card_verts (v w : V) [Fintype <| G.commonNeighbors v w] :
    Fintype.card (G.commonNeighbors v w) < Fintype.card V :=
  Nat.lt_of_le_of_lt (G.card_commonNeighbors_le_degree_left _ _) (G.degree_lt_card_verts v)

omit [Fintype V] in
variable {G} in
/-- If the condition `G.Adj v w` fails, then `card_commonNeighbors_le_degree` is
the best we can do in general. -/
theorem Adj.card_commonNeighbors_lt_degree {v w : V} [Fintype <| G.commonNeighbors v w]
    [Finite <| G.neighborSet v] (h : G.Adj v w) :
    Fintype.card (G.commonNeighbors v w) < G.degree v := by
  have := Fintype.ofFinite <| G.neighborSet v
  rw [← card_neighborSet_eq_degree]
  refine Set.card_lt_card <| Set.ssubset_iff_exists.mpr ⟨Set.inter_subset_left, w, h, ?_⟩
  exact G.notMem_commonNeighbors_right v w

theorem card_commonNeighbors_top {v w : V} (h : v ≠ w) [Fintype <| commonNeighbors ⊤ v w] :
    Fintype.card ((⊤ : SimpleGraph V).commonNeighbors v w) = Fintype.card V - 2 := by
  classical
  simp only [commonNeighbors_top_eq, ← Set.toFinset_card]
  simp [Finset.card_sdiff, h]

end Finite

namespace Iso

variable {G} {W : Type*} {G' : SimpleGraph W}

theorem card_edgeFinset_eq (f : G ≃g G') [Fintype G.edgeSet] [Fintype G'.edgeSet] :
    #G.edgeFinset = #G'.edgeFinset := by
  apply Finset.card_eq_of_equiv
  simp only [Set.mem_toFinset]
  exact f.mapEdgeSet

@[simp]
theorem degree_eq (f : G ≃g G') (x : V) : G'.degree (f x) = G.degree x :=
  Set.ncard_congr' <| mapNeighborSet f x |>.symm

theorem minDegree_eq (f : G ≃g G') : G.minDegree = G'.minDegree :=
  congrArg ENat.toNat <| f.surjective.iInf_congr f (Set.encard_congr <| mapNeighborSet f · |>.symm)

theorem maxDegree_eq (f : G ≃g G') : G.maxDegree = G'.maxDegree :=
  congrArg ENat.toNat <| f.surjective.iSup_congr f (Set.encard_congr <| mapNeighborSet f · |>.symm)

end Iso

section Support

variable {s : Set V} {G}

lemma edgeFinset_subset_sym2_of_support_subset [Fintype G.edgeSet] [Fintype s] (h : G.support ⊆ s) :
    G.edgeFinset ⊆ s.toFinset.sym2 := by
  simp_rw [subset_iff, Sym2.forall,
    mem_edgeFinset, mem_edgeSet, mk_mem_sym2_iff, Set.mem_toFinset]
  intro _ _ hadj
  exact ⟨h ⟨_, hadj⟩, h ⟨_, hadj.symm⟩⟩

instance [Fintype V] [DecidableRel G.Adj] : DecidablePred (· ∈ G.support) :=
  inferInstanceAs <| DecidablePred (· ∈ { v | ∃ w, G.Adj v w })

theorem map_edgeFinset_induce [DecidableEq V] [Fintype G.edgeSet] [Fintype (G.induce s).edgeSet]
    [Fintype s] :
    (G.induce s).edgeFinset.map (Embedding.subtype s).sym2Map = G.edgeFinset ∩ s.toFinset.sym2 := by
  simp_rw [Finset.ext_iff, Sym2.forall, mem_inter, mk_mem_sym2_iff, mem_map, Sym2.exists,
    Set.mem_toFinset, mem_edgeSet, comap_adj, Embedding.sym2Map_apply, Embedding.coe_subtype,
    Sym2.map_pair_eq, Sym2.eq_iff]
  refine fun v w ↦ ⟨?_, fun ⟨hadj, hv, hw⟩ ↦ ⟨⟨v, hv⟩, ⟨w, hw⟩, hadj, by tauto⟩⟩
  rintro ⟨x, y, hadj, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩
  exacts [⟨hadj, x.prop, y.prop⟩, ⟨hadj.symm, y.prop, x.prop⟩]

theorem map_edgeFinset_induce_of_support_subset [Fintype G.edgeSet] [Fintype (G.induce s).edgeSet]
    [Finite s] (h : G.support ⊆ s) :
    (G.induce s).edgeFinset.map (Embedding.subtype s).sym2Map = G.edgeFinset := by
  classical
  have := Fintype.ofFinite s
  simpa [map_edgeFinset_induce] using edgeFinset_subset_sym2_of_support_subset h

/-- If the support of the simple graph `G` is a subset of the set `s`, then the induced subgraph of
`s` has the same number of edges as `G`. -/
theorem card_edgeFinset_induce_of_support_subset [Fintype G.edgeSet] [Fintype (G.induce s).edgeSet]
    [Finite s] (h : G.support ⊆ s) : #(G.induce s).edgeFinset = #G.edgeFinset := by
  rw [← map_edgeFinset_induce_of_support_subset h, card_map]

theorem card_edgeFinset_induce_support [Fintype G.edgeSet] [Fintype (G.induce G.support).edgeSet]
    [Finite G.support] : #(G.induce G.support).edgeFinset = #G.edgeFinset :=
  card_edgeFinset_induce_of_support_subset subset_rfl

theorem map_neighborFinset_induce [DecidableEq V] (v : s) [Fintype <| G.neighborSet v]
    [Fintype <| (induce s G).neighborSet v] [Fintype s] :
    ((G.induce s).neighborFinset v).map (.subtype (· ∈ s)) = G.neighborFinset v ∩ s.toFinset := by
  ext; simp

theorem map_neighborFinset_induce_of_neighborSet_subset {v : s} [Fintype <| G.neighborSet v]
    [Fintype <| (induce s G).neighborSet v] [Fintype s] (h : G.neighborSet v ⊆ s) :
    ((G.induce s).neighborFinset v).map (.subtype s) = G.neighborFinset v := by
  classical
  rwa [← Set.toFinset_subset_toFinset, ← neighborFinset_def, ← inter_eq_left,
    ← map_neighborFinset_induce v] at h

/-- If the neighbor set of a vertex `v` is a subset of `s`, then the degree of the vertex in the
induced subgraph of `s` is the same as in `G`. -/
theorem degree_induce_of_neighborSet_subset {v : s} (h : G.neighborSet v ⊆ s) :
    (G.induce s).degree v = G.degree v :=
  Set.ncard_congr' <| .mk (fun u ↦ ⟨u, u.prop⟩) (fun u ↦ ⟨⟨u, h u.prop⟩, u.prop⟩)

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

variable {W : Type*} (f : V ↪ W) (G : SimpleGraph V) [Fintype G.edgeSet] [Fintype (G.map f).edgeSet]

@[simp]
theorem edgeFinset_map : (G.map f).edgeFinset = G.edgeFinset.map f.sym2Map := by
  classical
  rw [Finset.map_eq_image, ← Set.toFinset_image, Set.toFinset_inj]
  exact G.edgeSet_map f

theorem card_edgeFinset_map : #(G.map f).edgeFinset = #G.edgeFinset := by
  rw [edgeFinset_map]
  exact G.edgeFinset.card_map f.sym2Map

end Map

end SimpleGraph

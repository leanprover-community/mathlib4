/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `SimpleGraph.IsAcyclic` is a predicate for a graph having no cyclic walks.
* `SimpleGraph.IsTree` is a predicate for a graph being a tree (a connected acyclic graph).

## Main statements

* `SimpleGraph.isAcyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `SimpleGraph.isAcyclic_iff_forall_edge_isBridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `SimpleGraph.isTree_iff_existsUnique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `SimpleGraph.IsAcyclic` and `SimpleGraph.IsTree`, including
supporting lemmas about `SimpleGraph.IsBridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/


namespace SimpleGraph

open Walk

variable {V V' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V')

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff]
structure IsTree : Prop where
  /-- Graph is connected. -/
  protected isConnected : G.Connected
  /-- Graph is acyclic. -/
  protected IsAcyclic : G.IsAcyclic

variable {G G'}

@[simp] lemma isAcyclic_bot : IsAcyclic (⊥ : SimpleGraph V) := fun _a _w hw ↦ hw.ne_bot rfl

/-- A graph that has an injective homomorphism to an acyclic graph is acyclic. -/
lemma IsAcyclic.comap (f : G →g G') (hinj : Function.Injective f) (h : G'.IsAcyclic) :
    G.IsAcyclic :=
  fun _ _ ↦ map_isCycle_iff_of_injective hinj |>.not.mp <| h _

lemma IsAcyclic.embedding (f : G ↪g G') (h : G'.IsAcyclic) : G.IsAcyclic :=
  h.comap f f.injective

/-- Isomorphic graphs are acyclic together. -/
lemma Iso.isAcyclic_iff (f : G ≃g G') : G.IsAcyclic ↔ G'.IsAcyclic :=
  ⟨fun h ↦ h.embedding f.symm, fun h ↦ h.embedding f⟩

/-- Isomorphic graphs are trees together. -/
lemma Iso.isTree_iff (f : G ≃g G') : G.IsTree ↔ G'.IsTree :=
  ⟨fun ⟨hc, ha⟩ ↦ ⟨f.connected_iff.mp hc, f.isAcyclic_iff.mp ha⟩,
   fun ⟨hc, ha⟩ ↦ ⟨f.connected_iff.mpr hc, f.isAcyclic_iff.mpr ha⟩⟩

lemma IsAcyclic.of_map (f : V ↪ V') (h : G.map f |>.IsAcyclic) : G.IsAcyclic :=
  h.embedding <| SimpleGraph.Embedding.map ..

lemma IsAcyclic.of_comap (f : V' ↪ V) (h : G.IsAcyclic) : G.comap f |>.IsAcyclic :=
  h.embedding <| SimpleGraph.Embedding.comap ..

/-- A graph induced from an acyclic graph is acyclic. -/
lemma IsAcyclic.induce (h : G.IsAcyclic) (s : Set V) : G.induce s |>.IsAcyclic :=
  h.of_comap _

/-- A subgraph of an acyclic graph is acyclic. -/
lemma IsAcyclic.subgraph (h : G.IsAcyclic) (H : G.Subgraph) : H.coe.IsAcyclic :=
  h.comap _ H.hom_injective

/-- A spanning subgraph of an acyclic graph is acyclic. -/
lemma IsAcyclic.anti {G' : SimpleGraph V} (hsub : G ≤ G') (h : G'.IsAcyclic) : G.IsAcyclic :=
  h.comap ⟨_, fun h ↦ hsub h⟩ Function.injective_id

/-- A connected component of an acyclic graph is a tree. -/
lemma IsAcyclic.isTree_connectedComponent (h : G.IsAcyclic) (c : G.ConnectedComponent) :
    c.toSimpleGraph.IsTree where
  isConnected := c.connected_toSimpleGraph
  IsAcyclic := h.comap c.toSimpleGraph_hom <| by simp [ConnectedComponent.toSimpleGraph_hom]

theorem isAcyclic_iff_forall_adj_isBridge :
    G.IsAcyclic ↔ ∀ ⦃v w : V⦄, G.Adj v w → G.IsBridge s(v, w) := by
  simp_rw [isBridge_iff_adj_and_forall_cycle_notMem]
  constructor
  · intro ha v w hvw
    apply And.intro hvw
    intro u p hp
    cases ha p hp
  · rintro hb v (_ | ⟨ha, p⟩) hp
    · exact hp.not_of_nil
    · apply (hb ha).2 _ hp
      rw [Walk.edges_cons]
      apply List.mem_cons_self

theorem isAcyclic_iff_forall_edge_isBridge :
    G.IsAcyclic ↔ ∀ ⦃e⦄, e ∈ (G.edgeSet) → G.IsBridge e := by
  simp [isAcyclic_iff_forall_adj_isBridge, Sym2.forall]

theorem IsAcyclic.path_unique {G : SimpleGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w) :
    p = q := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  rw [Subtype.mk.injEq]
  induction p with
  | nil =>
    cases (Walk.isPath_iff_eq_nil _).mp hq
    rfl
  | cons ph p ih =>
    rw [isAcyclic_iff_forall_adj_isBridge] at h
    specialize h ph
    rw [isBridge_iff_adj_and_forall_walk_mem_edges] at h
    replace h := h.2 (q.append p.reverse)
    simp only [Walk.edges_append, Walk.edges_reverse, List.mem_append, List.mem_reverse] at h
    rcases h with h | h
    · cases q with
      | nil => simp at hp
      | cons _ q =>
        rw [Walk.cons_isPath_iff] at hp hq
        simp only [Walk.edges_cons, List.mem_cons, Sym2.eq_iff, true_and] at h
        rcases h with (⟨h, rfl⟩ | ⟨rfl, rfl⟩) | h
        · cases ih hp.1 q hq.1
          rfl
        · simp at hq
        · exact absurd (Walk.fst_mem_support_of_mem_edges _ h) hq.2
    · rw [Walk.cons_isPath_iff] at hp
      exact absurd (Walk.fst_mem_support_of_mem_edges _ h) hp.2

theorem isAcyclic_of_path_unique (h : ∀ (v w : V) (p q : G.Path v w), p = q) : G.IsAcyclic := by
  intro v c hc
  simp only [Walk.isCycle_def, Ne] at hc
  cases c with
  | nil => cases hc.2.1 rfl
  | cons ha c' =>
    simp only [Walk.cons_isTrail_iff, Walk.support_cons, List.tail_cons] at hc
    specialize h _ _ ⟨c', by simp only [Walk.isPath_def, hc.2]⟩ (Path.singleton ha.symm)
    rw [Path.singleton, Subtype.mk.injEq] at h
    simp [h] at hc

theorem isAcyclic_iff_path_unique : G.IsAcyclic ↔ ∀ ⦃v w : V⦄ (p q : G.Path v w), p = q :=
  ⟨IsAcyclic.path_unique, isAcyclic_of_path_unique⟩

theorem isTree_iff_existsUnique_path :
    G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath := by
  classical
  rw [isTree_iff, isAcyclic_iff_path_unique]
  constructor
  · rintro ⟨hc, hu⟩
    refine ⟨hc.nonempty, ?_⟩
    intro v w
    let q := (hc v w).some.toPath
    use q
    simp only [true_and, Path.isPath]
    intro p hp
    specialize hu ⟨p, hp⟩ q
    exact Subtype.ext_iff.mp hu
  · rintro ⟨hV, h⟩
    refine ⟨Connected.mk ?_, ?_⟩
    · intro v w
      obtain ⟨p, _⟩ := h v w
      exact p.reachable
    · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
      simp only [ExistsUnique.unique (h v w) hp hq]

lemma IsTree.existsUnique_path (hG : G.IsTree) : ∀ v w, ∃! p : G.Walk v w, p.IsPath :=
  (isTree_iff_existsUnique_path.1 hG).2

lemma IsTree.card_edgeFinset [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree) :
    Finset.card G.edgeFinset + 1 = Fintype.card V := by
  have := hG.isConnected.nonempty
  inhabit V
  classical
  have : Finset.card ({default} : Finset V)ᶜ + 1 = Fintype.card V := by
    rw [Finset.card_compl, Finset.card_singleton, Nat.sub_add_cancel Fintype.card_pos]
  rw [← this, add_left_inj]
  choose f hf hf' using (hG.existsUnique_path · default)
  refine Eq.symm <| Finset.card_bij
          (fun w hw => ((f w).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (by simpa using hw)
  case memEdges => simp
  case inj =>
    intro a ha b hb h
    wlog h' : (f a).length ≤ (f b).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_ge h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (by simpa using ha))] at h3
        cutsat
      · simp only [isPath_copy]
        exact (hf _).tail
  case surj =>
    simp only [mem_edgeFinset, Finset.mem_compl, Finset.mem_singleton, Sym2.forall, mem_edgeSet]
    intro x y h
    wlog h' : (f x).length ≤ (f y).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_ge h')
    refine ⟨y, ?_, dart_edge_eq_mk'_iff.2 <| Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ nil IsPath.nil, length_nil,
          ← hf' _ (.cons h .nil) (IsPath.nil.cons <| by simpa using h.ne),
          length_cons, length_nil] at h'
      simp at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _, fun hy => ?contra⟩)]
    · simp only [firstDart_toProd, getVert_cons_succ, getVert_zero, Prod.swap_prod_mk]
    case contra =>
      suffices (f x).takeUntil y hy = .cons h .nil by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

/-- A minimally connected graph is a tree. -/
lemma isTree_of_minimal_connected (h : Minimal Connected G) : IsTree G := by
  rw [isTree_iff, and_iff_right h.prop, isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ _ ↦ by_contra fun hbr ↦ h.not_prop_of_lt
    (by simpa [deleteEdges, ← edgeSet_ssubset_edgeSet])
    <| h.prop.connected_delete_edge_of_not_isBridge hbr

lemma isTree_iff_minimal_connected : IsTree G ↔ Minimal Connected G := by
  refine ⟨fun htree ↦ ⟨htree.isConnected, fun G' h' hle u v hadj ↦ ?_⟩, isTree_of_minimal_connected⟩
  have ⟨p, hp⟩ := h'.exists_isPath u v
  have := congrArg Walk.edges <| congrArg Subtype.val <|
    htree.IsAcyclic.path_unique ⟨p.mapLe hle, hp.mapLe hle⟩ <| Path.singleton hadj
  simp only [edges_map, Hom.coe_ofLE, Sym2.map_id, List.map_id_fun, id_eq] at this
  simp [this, p.adj_of_mem_edges]

/-- Every connected graph has a spanning tree. -/
lemma Connected.exists_isTree_le [Finite V] (h : G.Connected) : ∃ T ≤ G, IsTree T := by
  obtain ⟨T, hTG, hmin⟩ := {H : SimpleGraph V | H.Connected}.toFinite.exists_le_minimal h
  exact ⟨T, hTG, isTree_of_minimal_connected hmin⟩

/-- Every connected graph on `n` vertices has at least `n-1` edges. -/
lemma Connected.card_vert_le_card_edgeSet_add_one (h : G.Connected) :
    Nat.card V ≤ Nat.card G.edgeSet + 1 := by
  obtain hV | hV := (finite_or_infinite V).symm
  · simp
  have := Fintype.ofFinite
  obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
  rw [Nat.card_eq_fintype_card, ← hT.card_edgeFinset, add_le_add_iff_right,
    Nat.card_eq_fintype_card, ← edgeFinset_card]
  exact Finset.card_mono <| by simpa

lemma isTree_iff_connected_and_card [Finite V] :
    G.IsTree ↔ G.Connected ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
  have := Fintype.ofFinite V
  classical
  refine ⟨fun h ↦ ⟨h.isConnected, by simpa using h.card_edgeFinset⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
  simp_rw [isAcyclic_iff_forall_adj_isBridge]
  refine fun x y h ↦ by_contra fun hbr ↦
    (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_gt ?_
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, ← h₂, Nat.card_eq_fintype_card,
    ← edgeFinset_card, add_lt_add_iff_right]
  exact Finset.card_lt_card <| by simpa [deleteEdges]

/-- The minimum degree of all vertices in a nontrivial tree is one. -/
lemma IsTree.minDegree_eq_one_of_nontrivial (h : G.IsTree) [Fintype V] [Nontrivial V]
    [DecidableRel G.Adj] : G.minDegree = 1 := by
  by_cases q : 2 ≤ G.minDegree
  · have := h.card_edgeFinset
    have := G.sum_degrees_eq_twice_card_edges
    have hle : ∑ v : V, 2 ≤ ∑ v, G.degree v := by
      gcongr
      exact le_trans q (G.minDegree_le_degree _)
    rw [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hle
    cutsat
  · have := h.isConnected.preconnected.minDegree_pos_of_nontrivial
    cutsat

/-- A nontrivial tree has a vertex of degree one. -/
lemma IsTree.exists_vert_degree_one_of_nontrivial [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.IsTree) : ∃ v, G.degree v = 1 := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  use v
  rw [← hv]
  exact h.minDegree_eq_one_of_nontrivial

/-- The graph resulting from removing a vertex of degree one from a (pre)connected graph is
connected. -/
lemma Preconnected.connected_induce_complement_singleton_of_degree_eq_one [DecidableEq V]
    (hpreconn : G.Preconnected) {v : V} [Fintype ↑(G.neighborSet v)] (hdeg : G.degree v = 1) :
    (G.induce {v}ᶜ).Connected := by
  obtain ⟨u, adj_vu, hu⟩ := degree_eq_one_iff_unique_adj.mp hdeg
  refine (connected_iff _).mpr ⟨?_, ?_⟩
  /- There exists a walk between any two vertices w and x in G.induce {v}ᶜ
  via the unique vertex u adjacent to vertex v. -/
  · intro w x
    obtain ⟨pwu, hpwu⟩ := hpreconn.exists_isPath w u
    obtain ⟨pux, hpux⟩ := hpreconn.exists_isPath u x
    rw [Reachable, ← exists_true_iff_nonempty]
    use ((pwu.append pux).toPath.val.induce {v}ᶜ ?_).copy (SetCoe.ext rfl) (SetCoe.ext rfl)
    /- Each path between vertex u and another vertex in G.induce {v}ᶜ
    is contained in G.induce {v}ᶜ. -/
    intro z hz
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]
    obtain ⟨pwz, pzx, p_eq_pwzx⟩ := mem_support_iff_exists_append.mp hz
    /- Prove vertex v is not in the path formed from the concatenated walks
    by showing that vertex u must then be passed twice. -/
    by_contra
    subst_vars
    refine List.nodup_iff_forall_not_duplicate.mp (pwu.append pux).toPath.nodup_support u ?_
    rw [p_eq_pwzx, support_append, List.duplicate_iff_two_le_count, List.count_append]
    have := List.one_le_count_iff.mpr (pwz.getVert_mem_support (pwz.length - 1))
    simp only [hu _ (pwz.adj_penultimate (not_nil_of_ne (by aesop))).symm] at this
    have := List.one_le_count_iff.mpr (pzx.snd_mem_tail_support (not_nil_of_ne (by aesop)))
    rw [hu _ (pzx.adj_snd (not_nil_of_ne (by aesop)))] at this
    cutsat
  · rw [nonempty_subtype]
    use u
    aesop

/-- A finite nontrivial (pre)connected graph contains a vertex that leaves the graph connected if
removed. -/
lemma Preconnected.exists_vertex_connected_induce_complement_singleton_of_fintype_of_nontrivial
    [DecidableEq V] [Fintype V] [Nontrivial V] (hpreconn : G.Preconnected) :
    ∃ v : V, (G.induce {v}ᶜ).Connected := by
  obtain ⟨T, _, T_isTree⟩ := Connected.exists_isTree_le ⟨hpreconn⟩
  have ⟨hT, _⟩ := T_isTree
  have := Classical.decRel T.Adj
  obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial
  use v
  exact (hT.preconnected.connected_induce_complement_singleton_of_degree_eq_one hv).mono (by tauto)

/-- A finite connected graph contains a vertex that leaves the graph preconnected if removed. -/
lemma Connected.exists_vertex_preconnected_induce_complement_singleton_of_fintype
    [DecidableEq V] [Fintype V] (hconn : G.Connected) : ∃ v : V, (G.induce {v}ᶜ).Preconnected := by
  by_cases h : Nontrivial V
  · obtain ⟨v, hv⟩ :=
      Preconnected.exists_vertex_connected_induce_complement_singleton_of_fintype_of_nontrivial
      hconn.preconnected
    exact ⟨v, hv.preconnected⟩
  · use hconn.nonempty.some
    have := not_nontrivial_iff_subsingleton.mp h
    have : G.induce {hconn.nonempty.some}ᶜ = ⊥ := by
      ext w x
      simp [subsingleton_iff.mp _ w x]
    rw [this]
    exact preconnected_bot

end SimpleGraph

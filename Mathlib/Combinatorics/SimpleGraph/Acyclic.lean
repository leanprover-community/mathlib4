/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Bipartite
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Mathlib.Combinatorics.SimpleGraph.Metric

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

@[expose] public section


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

private lemma Walk.exists_mem_contains_edges_of_directed (Hs : Set <| SimpleGraph V)
    (hHs : Hs.Nonempty) (h_dir : DirectedOn (· ≤ ·) Hs) {u v : V} (p : (sSup Hs).Walk u v) :
    ∃ H ∈ Hs, ∀ e ∈ p.edges, e ∈ H.edgeSet := by
  induction p with
  | nil => exact ⟨hHs.some, hHs.some_mem, by simp⟩
  | @cons u v w h_adj p ih =>
    obtain ⟨H₁, hH₁, ih⟩ := ih
    obtain ⟨H₂, hH₂, h_adj⟩ : ∃ H₂ ∈ Hs, H₂.Adj u v := h_adj
    obtain ⟨H, hH, h₁, h₂⟩ := h_dir H₁ hH₁ H₂ hH₂
    simpa using ⟨H, hH, (le_iff_adj.mp h₂) _ _ h_adj, fun a ha => edgeSet_mono h₁ (ih a ha)⟩

/-- The directed supremum of acyclic graphs is acylic. -/
lemma isAcyclic_sSup_of_isAcyclic_directedOn (Hs : Set <| SimpleGraph V)
    (h_acyc : ∀ H ∈ Hs, H.IsAcyclic) (h_dir : DirectedOn (· ≤ ·) Hs) : IsAcyclic (sSup Hs) := by
  rcases Hs.eq_empty_or_nonempty with rfl | hnemp
  · simp
  · intro u p hp
    obtain ⟨H, hH, hpH⟩ := p.exists_mem_contains_edges_of_directed Hs hnemp h_dir
    exact h_acyc H hH (p.transfer H hpH) <| Walk.IsCycle.transfer hp hpH

/-- Every acyclic subgraph `H ≤ G` is contained in a maximal such subgraph. -/
theorem exists_maximal_isAcyclic_of_le_isAcyclic
    {H : SimpleGraph V} (hHG : H ≤ G) (hH : H.IsAcyclic) :
    ∃ H' : SimpleGraph V, H ≤ H' ∧ Maximal (fun H => H ≤ G ∧ H.IsAcyclic) H' := by
  refine zorn_le_nonempty₀ {H | H ≤ G ∧ H.IsAcyclic} (fun c hcs hc y hy ↦ ?_) _ ⟨hHG, hH⟩
  refine ⟨sSup c, ⟨?_, ?_⟩, CompleteLattice.le_sSup c⟩
  · grind [sSup_le_iff]
  · exact isAcyclic_sSup_of_isAcyclic_directedOn c (by grind) hc.directedOn

/-- A connected component of an acyclic graph is a tree. -/
lemma IsAcyclic.isTree_connectedComponent (h : G.IsAcyclic) (c : G.ConnectedComponent) :
    c.toSimpleGraph.IsTree where
  isConnected := c.connected_toSimpleGraph
  IsAcyclic := h.comap c.toSimpleGraph_hom <| by simp [ConnectedComponent.toSimpleGraph_hom]

lemma IsAcyclic.of_subsingleton [Subsingleton V] {G : SimpleGraph V} : G.IsAcyclic :=
  fun v p hp ↦ hp.ne_nil <| match p with
    | nil => rfl
    | cons hadj _ => (G.irrefl <| Subsingleton.elim v _ ▸ hadj).elim

lemma Subgraph.isAcyclic_coe_bot (G : SimpleGraph V) : (⊥ : G.Subgraph).coe.IsAcyclic :=
  @IsAcyclic.of_subsingleton _ (Set.isEmpty_coe_sort.mpr rfl).instSubsingleton _

lemma IsTree.of_subsingleton [Nonempty V] [Subsingleton V] {G : SimpleGraph V} : G.IsTree :=
  ⟨.of_subsingleton, .of_subsingleton⟩

theorem IsTree.coe_singletonSubgraph (G : SimpleGraph V) (v : V) :
    G.singletonSubgraph v |>.coe.IsTree :=
  .of_subsingleton

theorem IsTree.coe_subgraphOfAdj {u v : V} (h : G.Adj u v) : G.subgraphOfAdj h |>.coe.IsTree := by
  refine ⟨Subgraph.subgraphOfAdj_connected h, fun w p hp ↦ ?_⟩
  have : _ = _ := p.adj_snd <| nil_iff_eq_nil.not.mpr hp.ne_nil
  have : _ = _ := p.adj_penultimate <| nil_iff_eq_nil.not.mpr hp.ne_nil
  grind [Sym2.eq_iff, IsCycle.snd_ne_penultimate]

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
    simp only [Walk.isTrail_cons, Walk.support_cons, List.tail_cons] at hc
    specialize h _ _ ⟨c', by simp only [Walk.isPath_def, hc.2]⟩ (Path.singleton ha.symm)
    rw [Path.singleton, Subtype.mk.injEq] at h
    simp [h] at hc

theorem isAcyclic_iff_path_unique : G.IsAcyclic ↔ ∀ ⦃v w : V⦄ (p q : G.Path v w), p = q :=
  ⟨IsAcyclic.path_unique, isAcyclic_of_path_unique⟩

lemma IsAcyclic.mem_support_of_ne_mem_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hv : v ∉ q.support) : w ∈ p.support := by
  rw [Subtype.mk.inj <| isAcyclic_iff_path_unique.mp hG ⟨p, hp⟩ ⟨_, hq.concat hv hadj.symm⟩]
  exact q.support_subset_support_concat _ q.end_mem_support

lemma IsAcyclic.ne_mem_support_of_support_of_adj_of_isPath (hG : G.IsAcyclic) {u v w : V}
    {p : G.Walk u v} {q : G.Walk u w} (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w)
    (hw : w ∈ p.support) : v ∉ q.support := by
  obtain ⟨p₀, p₁, hp₀, hp₁, happend⟩ := hp.mem_support_iff_exists_append.mp hw
  rw [← Subtype.mk.inj <| hG.path_unique ⟨p₀, hp₀⟩ ⟨q, hq⟩]
  exact fun hxp => (happend ▸ hp).ne_of_mem_support_of_append hadj.symm.ne' hxp
    (p₁.end_mem_support) rfl

lemma IsAcyclic.path_concat (hG : G.IsAcyclic) {u v w : V} {p : G.Walk u v} {q : G.Walk u w}
    (hp : p.IsPath) (hq : q.IsPath) (hadj : G.Adj v w) (hv : v ∈ q.support) :
    q = p.concat hadj := by
  have hw : w ∉ p.support := hG.ne_mem_support_of_support_of_adj_of_isPath hq hp hadj.symm hv
  exact Subtype.mk.inj <| isAcyclic_iff_path_unique.mp hG ⟨q, hq⟩ ⟨_, hp.concat hw hadj⟩

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

theorem IsAcyclic.isPath_iff_isChain (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w) :
     p.IsPath ↔ List.IsChain (· ≠ ·) p.edges := by
  classical
  refine ⟨fun h ↦ (edges_nodup_of_support_nodup <| p.isPath_def.mp h).isChain, fun h ↦ ?_⟩
  induction p with
  | nil => simp
  | @cons u' v' _ head tail ih =>
    have hcc := List.isChain_cons.mp (edges_cons _ _ ▸ h)
    refine cons_isPath_iff head tail |>.mpr ⟨ih hcc.2, ?_⟩
    rcases tail.length.eq_zero_or_pos with h' | h'
    · simp [nil_iff_support_eq.mp (nil_iff_length_eq.mpr h'), head.ne]
    · by_contra hh
      apply hG <| cons head (tail.takeUntil u' hh)
      simp only [isCycle_def, isTrail_def, edges_cons, List.nodup_cons, ne_eq, reduceCtorEq,
        not_false_eq_true, support_cons, List.tail_cons, true_and]
      have : cons head (tail.takeUntil u' hh) |>.support.tail.Nodup :=
        tail.isPath_def.mp (ih hcc.2) |>.sublist <| List.IsInfix.sublist
          ⟨[], (tail.dropUntil u' hh).support.tail, by simp [← support_append]⟩
      refine ⟨⟨?_, edges_nodup_of_support_nodup this⟩, this⟩
      by_contra hhh
      refine hcc.1 s(u', v') ?_ rfl
      rw [← tail.cons_tail_eq (by simp [not_nil_iff_lt_length, h'])]
      have := IsPath.mk' this |>.eq_snd_of_mem_edges (Sym2.eq_swap ▸ hhh)
      simp [this, snd_takeUntil head.ne]

theorem IsAcyclic.isPath_iff_isTrail (hG : G.IsAcyclic) {v w : V} (p : G.Walk v w) :
    p.IsPath ↔ p.IsTrail :=
  ⟨IsPath.isTrail, fun h ↦ hG.isPath_iff_isChain p |>.mpr <| p.isTrail_def.mp h |>.isChain⟩

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
        lia
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
    lia
  · have := h.isConnected.preconnected.minDegree_pos_of_nontrivial
    lia

/-- A nontrivial tree has a vertex of degree one. -/
lemma IsTree.exists_vert_degree_one_of_nontrivial [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (h : G.IsTree) : ∃ v, G.degree v = 1 := by
  obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
  use v
  rw [← hv]
  exact h.minDegree_eq_one_of_nontrivial

/-- The graph resulting from removing a vertex of degree one from a connected graph is connected. -/
lemma Connected.induce_compl_singleton_of_degree_eq_one (hconn : G.Connected) {v : V}
    [Fintype ↑(G.neighborSet v)] (hdeg : G.degree v = 1) : (G.induce {v}ᶜ).Connected := by
  obtain ⟨u, adj_vu, hu⟩ := degree_eq_one_iff_existsUnique_adj.mp hdeg
  refine (connected_iff _).mpr ⟨?_, u, by aesop⟩
  /- There exists a walk between any two vertices w and x in G.induce {v}ᶜ
  via the unique vertex u adjacent to vertex v. -/
  intro w x
  obtain ⟨pwu, hpwu⟩ := hconn.exists_isPath w u
  obtain ⟨pux, hpux⟩ := hconn.exists_isPath u x
  rw [Reachable, ← exists_true_iff_nonempty]
  classical
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
  lia

/-- A finite nontrivial connected graph contains a vertex that leaves the graph connected if
removed. -/
lemma Connected.exists_connected_induce_compl_singleton_of_finite_nontrivial
    [Finite V] [Nontrivial V] (hconn : G.Connected) : ∃ v : V, (G.induce {v}ᶜ).Connected := by
  obtain ⟨T, _, T_isTree⟩ := hconn.exists_isTree_le
  have ⟨hT, _⟩ := T_isTree
  have := Fintype.ofFinite V
  classical
  obtain ⟨v, hv⟩ := T_isTree.exists_vert_degree_one_of_nontrivial
  exact ⟨v, (hT.induce_compl_singleton_of_degree_eq_one hv).mono (by tauto)⟩

/-- A finite connected graph contains a vertex that leaves the graph preconnected if removed. -/
lemma Connected.exists_preconnected_induce_compl_singleton_of_finite [Finite V]
    (hconn : G.Connected) : ∃ v : V, (G.induce {v}ᶜ).Preconnected := by
  nontriviality V using hconn.nonempty
  obtain ⟨v, hv⟩ := hconn.exists_connected_induce_compl_singleton_of_finite_nontrivial
  exact ⟨v, hv.preconnected⟩

lemma IsAcyclic.dist_ne_of_adj (hG : G.IsAcyclic) {u v w : V} (hadj : G.Adj v w)
    (hreach : G.Reachable u v) : G.dist u v ≠ G.dist u w := by
  obtain ⟨p, hp, hp'⟩ := hreach.exists_path_of_dist
  obtain ⟨q, hq, hq'⟩ := hreach.trans hadj.reachable |>.exists_path_of_dist
  rw [← hp', ← hq']
  by_cases hw : w ∈ p.support
  · rw [hG.path_concat hq hp hadj.symm hw, q.length_concat]
    exact q.length.ne_add_one.symm
  · have hv : v ∈ q.support := hG.mem_support_of_ne_mem_support_of_adj_of_isPath hq hp
      hadj.symm hw
    rw [hG.path_concat hp hq hadj hv, p.length_concat]
    exact p.length.ne_add_one

lemma IsTree.dist_ne_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w) :
    G.dist u v ≠ G.dist u w :=
  hG.IsAcyclic.dist_ne_of_adj hadj <| hG.isConnected u v

lemma IsAcyclic.dist_eq_dist_add_one_of_adj_of_reachable
    (hG : G.IsAcyclic) (u : V) {v w : V} (hadj : G.Adj v w) (hreach : G.Reachable u v) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1 := by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

lemma IsTree.dist_eq_dist_add_one_of_adj (hG : G.IsTree) (u : V) {v w : V} (hadj : G.Adj v w) :
    G.dist u v = G.dist u w + 1 ∨ G.dist u w = G.dist u v + 1 := by
  grind [dist_ne_of_adj, Adj.diff_dist_adj]

/-- The unique two-coloring of a tree that colors the given vertex with zero -/
noncomputable def IsTree.coloringTwoOfVert (hG : G.IsTree) (u : V) : G.Coloring (Fin 2) :=
  Coloring.mk (fun v ↦ ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩) <| by
    grind [dist_eq_dist_add_one_of_adj]

/-- Arbitrary coloring with two colors for a tree -/
noncomputable def IsTree.coloringTwo (hG : G.IsTree) : G.Coloring (Fin 2) :=
  hG.coloringTwoOfVert hG.isConnected.nonempty.some

lemma IsTree.isBipartite (hG : G.IsTree) : G.IsBipartite :=
  ⟨hG.coloringTwo⟩

/-- The unique two-coloring of a forest that colors the given vertices with zero -/
noncomputable def IsAcyclic.coloringTwoOfVerts (hG : G.IsAcyclic) (verts : G.ConnectedComponent → V)
    (h : ∀ C, verts C ∈ C) : G.Coloring (Fin 2) where
  toFun v :=
    let u := verts <| G.connectedComponentMk v
    ⟨G.dist u v % 2, Nat.mod_lt (G.dist u v) Nat.zero_lt_two⟩
  map_rel' := by
    intro u v hadj
    have := ConnectedComponent.sound hadj.reachable
    have := hG.dist_eq_dist_add_one_of_adj_of_reachable _ hadj <| ConnectedComponent.exact <| h _
    grind [top_adj]

/-- Arbitrary coloring with two colors for a forest -/
noncomputable def IsAcyclic.coloringTwo (hG : G.IsAcyclic) : G.Coloring (Fin 2) :=
  hG.coloringTwoOfVerts (·.nonempty_supp.some) (·.nonempty_supp.some_mem)

lemma IsAcyclic.isBipartite (hG : G.IsAcyclic) : G.IsBipartite :=
  ⟨hG.coloringTwo⟩

end SimpleGraph

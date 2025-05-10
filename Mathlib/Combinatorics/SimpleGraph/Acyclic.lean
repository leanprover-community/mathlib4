/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Data.Fintype.Order
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Combinatorics.SimpleGraph.Operations

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


universe u v

namespace SimpleGraph

open Walk

variable {V : Type u} (G : SimpleGraph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff]
structure IsTree : Prop where
  /-- Graph is connected. -/
  protected isConnected : G.Connected
  /-- Graph is acyclic. -/
  protected IsAcyclic : G.IsAcyclic

variable {G}

@[simp] lemma isAcyclic_bot : IsAcyclic (⊥ : SimpleGraph V) := fun _a _w hw ↦ hw.ne_bot rfl

theorem isAcyclic_iff_forall_adj_isBridge :
    G.IsAcyclic ↔ ∀ ⦃v w : V⦄, G.Adj v w → G.IsBridge s(v, w) := by
  simp_rw [isBridge_iff_adj_and_forall_cycle_not_mem]
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
      | nil => simp [Walk.isPath_def] at hp
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
    intros a ha b hb h
    wlog h' : (f a).length ≤ (f b).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_le h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ ((f _).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (by simpa using ha))] at h3
        omega
      · simp only [ne_eq, eq_mp_eq_cast, id_eq, isPath_copy]
        exact (hf _).tail
  case surj =>
    simp only [mem_edgeFinset, Finset.mem_compl, Finset.mem_singleton, Sym2.forall, mem_edgeSet]
    intros x y h
    wlog h' : (f x).length ≤ (f y).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_le h')
    refine ⟨y, ?_, dart_edge_eq_mk'_iff.2 <| Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ nil IsPath.nil, length_nil,
          ← hf' _ (.cons h .nil) (IsPath.nil.cons <| by simpa using h.ne),
          length_cons, length_nil] at h'
      simp [Nat.le_zero, Nat.one_ne_zero] at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _, fun hy => ?contra⟩)]
    · simp only [firstDart_toProd, getVert_cons_succ, getVert_zero, Prod.swap_prod_mk]
    case contra =>
      suffices (f x).takeUntil y hy = .cons h .nil by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

theorem maximal_isAcyclic_iff_isTree [Nonempty V] :  Maximal IsAcyclic G ↔ G.IsTree where
  mp := by

    intro ⟨hIsAcyclic, hmaximal⟩
    refine ⟨?_, hIsAcyclic⟩
    rw [connected_iff]
    refine ⟨?_, by assumption⟩
    by_contra hnot_Preconnected
    simp only [Preconnected, not_forall] at hnot_Preconnected
    rcases hnot_Preconnected with ⟨u, v, hnot_Reachable⟩
    have hnot_Adj_uv : ¬ G.Adj u v := fun x ↦ hnot_Reachable (Adj.reachable x)
    let y := G ⊔ edge u v
    have hy_not_Acyclic : ¬ y.IsAcyclic := by
      by_contra hy_Acyclic
      specialize hmaximal hy_Acyclic le_sup_left
      simp_all only [le_sup_left, imp_self, sup_le_iff, le_refl, true_and, sup_of_le_left, y]
      have h : (u = u ∧ v = v ∨ u = v ∧ v = u) ∧ u ≠ v := by
        refine ⟨by aesop, ?_⟩
        by_contra hu_eq_v
        rw [hu_eq_v] at hnot_Reachable
        exact hnot_Reachable (Reachable.refl v)
      rw [← edge_adj u v u v] at h
      exact hnot_Adj_uv (hmaximal h)
    simp only [IsAcyclic, not_forall, not_not] at hy_not_Acyclic
    rcases hy_not_Acyclic with ⟨w, x, hx⟩
    have huv_in_cycle : s(u, v) ∈ edges x := by
      by_contra hnot_uv_in_cycle
      have he_in_G : ∀ e ∈ x.edges, e ∈ G.edgeSet := by
        intro e he
        have he_in_y : e ∈ y.edgeSet := edges_subset_edgeSet x he
        rw [edgeSet_sup] at he_in_y
        rcases he_in_y with _ | he_eq_uv
        · assumption
        · have huvne : u ≠ v := by
            by_contra hu_eq_v
            apply hnot_Reachable
            rw [hu_eq_v]
          rw [edge_edgeSet_of_ne huvne] at he_eq_uv
          rw [he_eq_uv] at he
          cases hnot_uv_in_cycle he
      exact hIsAcyclic (x.transfer G he_in_G) (IsCycle.transfer hx he_in_G)
    have hReachable :=
      (adj_and_reachable_delete_edges_iff_exists_cycle.2 ⟨w, x, hx, huv_in_cycle⟩).2
    have hG_add_minus : (y \ fromEdgeSet {s(u, v)}) = G := by
      ext a b
      simp only [sdiff_adj, sup_adj, fromEdgeSet_adj,
        Set.mem_singleton_iff, Sym2.eq, Sym2.rel_iff', Prod.mk.injEq, Prod.swap_prod_mk, ne_eq,
        not_and, Decidable.not_not, y]
      rw [edge_adj]
      refine ⟨by aesop, ?_⟩
      intro hAdj_ab
      simp_all only [true_or, true_and]
      rintro (_ | ⟨rfl, rfl⟩)
      · simp_all
      · exfalso
        exact hnot_Adj_uv (adj_symm G hAdj_ab)
    rw [hG_add_minus] at hReachable
    exact hnot_Reachable hReachable
  mpr := by
    intro h_IsTree
    refine ⟨h_IsTree.IsAcyclic, ?_⟩
    intro y hy hG u v huv
    by_contra hnot_Adj_uv
    rcases h_IsTree with ⟨⟨h_Preconnected⟩, _⟩
    specialize h_Preconnected u v
    rcases h_Preconnected with ⟨gwalk⟩
    classical
    let ypath := (gwalk.bypass).mapLe hG
    have hvu := (adj_symm y huv)
    let ycycle := cons hvu ypath
    apply hy ycycle
    rw [cons_isCycle_iff ypath hvu]
    refine ⟨IsPath.mapLe hG (bypass_isPath gwalk),
      List.forall_mem_ne.mp ?_⟩
    intro e he
    by_contra he_in_path
    have hypath_edges : ypath.edges = _ :=
      edges_map (Hom.mapSpanningSubgraphs hG) gwalk.bypass
    rw [hypath_edges, ← he_in_path, List.mem_map] at he
    rcases he with ⟨a, ha_in_path, hmap_a_eq⟩
    simp only [Hom.mapSpanningSubgraphs_apply, Sym2.map_id', id_eq] at hmap_a_eq
    have ha := edges_subset_edgeSet gwalk.bypass ha_in_path
    rw [hmap_a_eq, mem_edgeSet G] at ha
    exact hnot_Adj_uv (adj_symm G ha)

/-- A minimally connected graph is a tree. -/
lemma isTree_of_minimal_connected (h : Minimal Connected G) : IsTree G := by
  rw [isTree_iff, and_iff_right h.prop, isAcyclic_iff_forall_adj_isBridge]
  exact fun _ _ _↦ by_contra fun hbr ↦ h.not_prop_of_lt
    (by simpa [deleteEdges, ← edgeSet_ssubset_edgeSet])
    <| h.prop.connected_delete_edge_of_not_isBridge hbr

/-- Every connected graph has a spanning tree. -/
lemma Connected.exists_isTree_le [Finite V] (h : G.Connected) : ∃ T ≤ G, IsTree T := by
  obtain ⟨T, hTG, hmin⟩ := {H : SimpleGraph V | H.Connected}.toFinite.exists_minimal_le h
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
    (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_lt ?_
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, ← h₂, Nat.card_eq_fintype_card,
    ← edgeFinset_card, add_lt_add_iff_right]
  exact Finset.card_lt_card <| by simpa [deleteEdges]

end SimpleGraph

/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity
import Mathlib.Tactic.Linarith

#align_import combinatorics.simple_graph.acyclic from "leanprover-community/mathlib"@"b07688016d62f81d14508ff339ea3415558d6353"

/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `SimpleGraph.IsAcyclic` is a predicate for a graph having no cyclic walks
* `SimpleGraph.IsTree` is a predicate for a graph being a tree (a connected acyclic graph)

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
#align simple_graph.is_acyclic SimpleGraph.IsAcyclic

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff]
structure IsTree : Prop where
  /-- Graph is connected. -/
  protected isConnected : G.Connected
  /-- Graph is acyclic. -/
  protected IsAcyclic : G.IsAcyclic
#align simple_graph.is_tree SimpleGraph.IsTree

variable {G}

theorem isAcyclic_iff_forall_adj_isBridge :
    G.IsAcyclic ↔ ∀ ⦃v w : V⦄, G.Adj v w → G.IsBridge ⟦(v, w)⟧ := by
  simp_rw [isBridge_iff_adj_and_forall_cycle_not_mem]
  -- ⊢ IsAcyclic G ↔ ∀ ⦃v w : V⦄, Adj G v w → Adj G v w ∧ ∀ ⦃u : V⦄ (p : Walk G u u …
  constructor
  -- ⊢ IsAcyclic G → ∀ ⦃v w : V⦄, Adj G v w → Adj G v w ∧ ∀ ⦃u : V⦄ (p : Walk G u u …
  · intro ha v w hvw
    -- ⊢ Adj G v w ∧ ∀ ⦃u : V⦄ (p : Walk G u u), IsCycle p → ¬Quotient.mk (Sym2.Rel.s …
    apply And.intro hvw
    -- ⊢ ∀ ⦃u : V⦄ (p : Walk G u u), IsCycle p → ¬Quotient.mk (Sym2.Rel.setoid V) (v, …
    intro u p hp
    -- ⊢ ¬Quotient.mk (Sym2.Rel.setoid V) (v, w) ∈ edges p
    cases ha p hp
    -- 🎉 no goals
  · rintro hb v (_ | ⟨ha, p⟩) hp
    -- ⊢ False
    · exact hp.not_of_nil
      -- 🎉 no goals
    · apply (hb ha).2 _ hp
      -- ⊢ Quotient.mk (Sym2.Rel.setoid V) (v, v✝) ∈ edges (cons ha p)
      rw [Walk.edges_cons]
      -- ⊢ Quotient.mk (Sym2.Rel.setoid V) (v, v✝) ∈ Quotient.mk (Sym2.Rel.setoid V) (v …
      apply List.mem_cons_self
      -- 🎉 no goals
#align simple_graph.is_acyclic_iff_forall_adj_is_bridge SimpleGraph.isAcyclic_iff_forall_adj_isBridge

theorem isAcyclic_iff_forall_edge_isBridge :
    G.IsAcyclic ↔ ∀ ⦃e⦄, e ∈ (G.edgeSet) → G.IsBridge e := by
  simp [isAcyclic_iff_forall_adj_isBridge, Sym2.forall]
  -- 🎉 no goals
#align simple_graph.is_acyclic_iff_forall_edge_is_bridge SimpleGraph.isAcyclic_iff_forall_edge_isBridge

theorem IsAcyclic.path_unique {G : SimpleGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w) :
    p = q := by
  obtain ⟨p, hp⟩ := p
  -- ⊢ { val := p, property := hp } = q
  obtain ⟨q, hq⟩ := q
  -- ⊢ { val := p, property := hp } = { val := q, property := hq }
  rw [Subtype.mk.injEq]
  -- ⊢ p = q
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
    cases' h with h h
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
#align simple_graph.is_acyclic.path_unique SimpleGraph.IsAcyclic.path_unique

theorem isAcyclic_of_path_unique (h : ∀ (v w : V) (p q : G.Path v w), p = q) : G.IsAcyclic := by
  intro v c hc
  -- ⊢ False
  simp only [Walk.isCycle_def, Ne.def] at hc
  -- ⊢ False
  cases c with
  | nil => cases hc.2.1 rfl
  | cons ha c' =>
    simp only [Walk.cons_isTrail_iff, Walk.support_cons, List.tail_cons, true_and_iff] at hc
    specialize h _ _ ⟨c', by simp only [Walk.isPath_def, hc.2]⟩ (Path.singleton ha.symm)
    rw [Path.singleton, Subtype.mk.injEq] at h
    simp [h] at hc
#align simple_graph.is_acyclic_of_path_unique SimpleGraph.isAcyclic_of_path_unique

theorem isAcyclic_iff_path_unique : G.IsAcyclic ↔ ∀ ⦃v w : V⦄ (p q : G.Path v w), p = q :=
  ⟨IsAcyclic.path_unique, isAcyclic_of_path_unique⟩
#align simple_graph.is_acyclic_iff_path_unique SimpleGraph.isAcyclic_iff_path_unique

theorem isTree_iff_existsUnique_path :
    G.IsTree ↔ Nonempty V ∧ ∀ v w : V, ∃! p : G.Walk v w, p.IsPath := by
  classical
  rw [IsTree_iff, isAcyclic_iff_path_unique]
  constructor
  · rintro ⟨hc, hu⟩
    refine ⟨hc.nonempty, ?_⟩
    intro v w
    let q := (hc v w).some.toPath
    use q
    simp only [true_and_iff, Path.isPath]
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
#align simple_graph.is_tree_iff_exists_unique_path SimpleGraph.isTree_iff_existsUnique_path

lemma IsTree.existsUnique_path (hG : G.IsTree) : ∀ v w, ∃! p : G.Walk v w, p.IsPath :=
  (isTree_iff_existsUnique_path.1 hG).2

lemma IsTree.card_edgeFinset [Fintype V] [Fintype G.edgeSet] (hG : G.IsTree) :
    Finset.card G.edgeFinset + 1 = Fintype.card V := by
  have := hG.isConnected.nonempty
  -- ⊢ Finset.card (edgeFinset G) + 1 = Fintype.card V
  inhabit V
  -- ⊢ Finset.card (edgeFinset G) + 1 = Fintype.card V
  classical
  have : Finset.card ({default} : Finset V)ᶜ + 1 = Fintype.card V := by
    rw [Finset.card_compl, Finset.card_singleton, Nat.sub_add_cancel Fintype.card_pos]
  rw [← this, add_left_inj]
  choose f hf hf' using (hG.existsUnique_path · default)
  refine Eq.symm <| Finset.card_congr
          (fun w hw => ((f w).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (by simpa using hw)
  case memEdges => simp
  case inj =>
    intros a b ha hb h
    wlog h' : (f a).length ≤ (f b).length generalizing a b
    · exact Eq.symm (this _ _ hb ha h.symm (le_of_not_le h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a).firstDart <| not_nil_of_ne (by simpa using ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ (((f _).tail _).copy h1 rfl) ?_)
      rw [length_copy, ← add_left_inj 1, length_tail_add_one] at h3
      · exfalso
        linarith
      · simp only [ne_eq, eq_mp_eq_cast, id_eq, isPath_copy]
        exact (hf _).tail _
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
      simp [le_zero_iff, Nat.one_ne_zero] at h'
    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _, fun hy => ?contra⟩)]
    rfl
    case contra =>
      suffices : (f x).takeUntil y hy = .cons h .nil
      · rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

end SimpleGraph

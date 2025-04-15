/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.MyGraph.Pathverts
import Mathlib.Data.Fintype.Order
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!

# Acyclic graphs and trees

This module introduces *acyclic graphs* (a.k.a. *forests*) and *trees*.

## Main definitions

* `MyGraph.IsAcyclic` is a predicate for a graph having no cyclic walks.
* `MyGraph.IsTree` is a predicate for a graph being a tree (a connected acyclic graph).

## Main statements

* `MyGraph.isAcyclic_iff_path_unique` characterizes acyclicity in terms of uniqueness of
  paths between pairs of vertices.
* `MyGraph.isAcyclic_iff_forall_edge_isBridge` characterizes acyclicity in terms of every
  edge being a bridge edge.
* `MyGraph.isTree_iff_existsUnique_path` characterizes trees in terms of existence and
  uniqueness of paths between pairs of vertices from a nonempty vertex type.

## References

The structure of the proofs for `MyGraph.IsAcyclic` and `MyGraph.IsTree`, including
supporting lemmas about `MyGraph.IsBridge`, generally follows the high-level description
for these theorems for multigraphs from [Chou1994].

## Tags

acyclic graphs, trees
-/


universe u v
variable {V : Type u}
namespace MyGraph

open Walk

variable (G : MyGraph V)

/-- A graph is *acyclic* (or a *forest*) if it has no cycles. -/
def IsAcyclic : Prop := ∀ ⦃v : V⦄ (c : G.Walk v v), ¬c.IsCycle

/-- A *tree* is a preconnected acyclic graph. -/
@[mk_iff]
structure IsTree : Prop where
  /-- Graph is connected. -/
  protected isPreconnected : G.Preconnected
  /-- Graph is acyclic. -/
  protected IsAcyclic : G.IsAcyclic

variable {G}

@[simp] lemma isAcyclic_bot : IsAcyclic (⊥ : MyGraph V) := fun _a _w hw ↦ hw.ne_bot rfl

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

theorem IsAcyclic.path_unique {G : MyGraph V} (h : G.IsAcyclic) {v w : V} (p q : G.Path v w) :
    p = q := by
  obtain ⟨p, hp⟩ := p
  obtain ⟨q, hq⟩ := q
  rw [Subtype.mk.injEq]
  induction p with
  | nil hu =>
    rw [(Walk.isPath_iff_eq_nil _).mp hq]
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
    G.IsTree ↔  ∀ {v w : V}, v ∈ G.verts → w ∈ G.verts → ∃! p : G.Walk v w, p.IsPath := by
  classical
  rw [isTree_iff, isAcyclic_iff_path_unique]
  constructor
  · rintro ⟨hc, hu⟩
    intro v w hv hw
    let q := (hc hv hw).some.toPath
    use q
    simp only [true_and, Path.isPath]
    intro p hp
    specialize hu ⟨p, hp⟩ q
    exact Subtype.ext_iff.mp hu
  · intro h
    refine ⟨?_, ?_⟩
    · intro v w hv hw
      obtain ⟨p, _⟩ := h hv hw
      exact p.reachable
    · rintro v w ⟨p, hp⟩ ⟨q, hq⟩
      simp only [ExistsUnique.unique (h p.start_mem_verts p.end_mem_verts) hp hq]

lemma IsTree.existsUnique_path (hG : G.IsTree) :
    ∀ {v w}, v ∈ G.verts → w ∈ G.verts → ∃! p : G.Walk v w, p.IsPath := by
  intro v w hv hw; exact isTree_iff_existsUnique_path.1 hG hv hw

open Finset
lemma IsTree.card_edgeFinset [DecidableEq V] [Fintype G.verts] [Fintype G.edgeSet] {v : V}
    (hG : G.IsTree) (hv : v ∈ G.verts) :
      #G.edgeFinset + 1 = #G.vertsFinset := by
  have : #(G.vertsFinset.erase v) + 1 =  #G.vertsFinset := by
    rw [Finset.card_erase_of_mem (by simpa using hv),  Nat.sub_add_cancel ]
    exact Finset.card_pos.2  (by simpa using ⟨v, hv⟩)
  rw [← this, add_left_inj]
  choose f hf hf' using (@hG.existsUnique_path _ _ · v )
  have hm {x : V} : x ∈ G.verts.toFinset.erase v → x ∈ G.verts := by simp
  have hm'{x : V} : x ∈ G.verts.toFinset.erase v → x ≠ v := by rintro h rfl; simp at h
  refine Eq.symm <| Finset.card_bij
          (fun w hw => ((f w  (hm hw) hv).firstDart <| ?notNil).edge)
          (fun a ha => ?memEdges) ?inj ?surj
  case notNil => exact not_nil_of_ne (hm' hw)
  case memEdges => simp
  case inj =>
    intros a ha b hb h
    wlog h' : (f a (hm ha) hv).length ≤ (f b (hm hb) hv).length generalizing a b
    · exact Eq.symm (this _ hb _ ha h.symm (le_of_not_le h'))
    rw [dart_edge_eq_iff] at h
    obtain (h | h) := h
    · exact (congrArg (·.fst) h)
    · have h1 : ((f a (hm ha) hv).firstDart <| not_nil_of_ne (hm' ha)).snd = b :=
        congrArg (·.snd) h
      have h3 := congrArg length (hf' _ (hm hb) hv ((f _ (hm ha) hv).tail.copy h1 rfl) ?_)
      · rw [length_copy, ← add_left_inj 1,
          length_tail_add_one (not_nil_of_ne (hm' ha))] at h3
        omega
      · simp only [ne_eq, eq_mp_eq_cast, id_eq, isPath_copy]
        exact (hf a (hm ha) hv).tail
  case surj =>
    simp only [Set.mem_toFinset, Finset.mem_erase, ne_eq, Sym2.forall, mem_edgeSet]
    intros x y h
    wlog h' : (f x h.mem_verts hv).length ≤ (f y h.mem_verts' hv).length generalizing x y
    · rw [Sym2.eq_swap]
      exact this y x h.symm (le_of_not_le h')
    refine ⟨y, ⟨?_, h.mem_verts'⟩, dart_edge_eq_mk'_iff.2 <| Or.inr ?_⟩
    · rintro rfl
      rw [← hf' _ h.mem_verts' hv (nil hv) (IsPath.nil hv), length_nil,
          ← hf' _ h.mem_verts hv (.cons h (.nil hv)) ((IsPath.nil hv).cons <| by simpa using h.ne),
          length_cons, length_nil] at h'
      simp [Nat.le_zero, Nat.one_ne_zero] at h'
    rw [← hf' _ h.mem_verts' hv (.cons h.symm (f x h.mem_verts hv)) ((cons_isPath_iff _ _).2
      ⟨hf _ h.mem_verts hv, fun hy => ?contra⟩)]
    · simp only [firstDart_toProd, getVert_cons_succ, getVert_zero, Prod.swap_prod_mk]
    case contra =>
      suffices (f _ h.mem_verts hv).takeUntil y hy = .cons h (.nil (h.mem_verts')) by
        rw [← take_spec _ hy, hf' _ h.mem_verts' hv _ ((hf _ h.mem_verts hv).dropUntil hy)] at h'
        simp [this] at h'
      exact (hG.existsUnique_path h.mem_verts h.mem_verts').unique
                    ((hf _ _ hv).takeUntil _) (by simp [h.ne])

/-- A minimally connected graph is a tree. -/
lemma isTree_of_minimal_preconnected (h : Minimal Preconnected G) : IsTree G := by
  rw [isTree_iff]
  constructor
  · exact h.prop
  · rw [ isAcyclic_iff_forall_adj_isBridge]
    intro x y hxy
    by_contra! hbr
    exact h.not_prop_of_lt (G.deleteEdges_lt hxy (by simp))
        <| G.preconnected_delete_edge_of_not_isBridge h.prop hbr

/-- Every preconnected graph has a spanning tree. -/
lemma Preconnected.exists_isTree_le [Finite V] (h : G.Preconnected) : ∃ T ≤ G, IsTree T := by
  obtain ⟨T, hTG, hmin⟩ := {H : MyGraph V | H.Preconnected}.toFinite.exists_minimal_le h
  exact ⟨T, hTG, isTree_of_minimal_preconnected hmin⟩

/-- Every preconnected graph has a spanning tree. -/
lemma Preconnected.exists_isTree_le' [Finite G.verts] (h : G.Preconnected) : ∃ T ≤ G, IsTree T := by
  haveI hf : Finite {H : MyGraph V | H ≤ G} := by sorry
  haveI : Finite {H : MyGraph V | H ≤ G ∧ H.Preconnected} := Set.Finite.subset hf (fun _ h' ↦ h'.1)
  have : G ≤ G ∧ G.Preconnected := ⟨le_refl _, h⟩
  obtain ⟨T, hTG, hmin⟩ := {H : MyGraph V | H ≤ G ∧ H.Preconnected}.toFinite.exists_minimal_le this
  have hmin' : Minimal Preconnected T := by
    constructor
    · exact hmin.prop.2
    · intro H hH hle
      exact hmin.2 ⟨hle.trans hTG, hH⟩ hle
  exact ⟨T, hTG, isTree_of_minimal_preconnected hmin'⟩


-- /-- Every connected graph on `n` vertices has at least `n-1` edges. -/
-- lemma Preconnected.card_vert_le_card_edgeSet_add_one (h : G.Preconnected) :
--     Nat.card G.verts ≤ Nat.card G.edgeSet + 1 := by
--   obtain hV | hV := (finite_or_infinite G.verts).symm
--   · simp
--   have := Fintype.ofFinite
--   obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
--   rw [Nat.card_eq_fintype_card, ← hT.card_edgeFinset, add_le_add_iff_right,
--     Nat.card_eq_fintype_card, ← edgeFinset_card]
--   exact Finset.card_mono <| by simpa



end MyGraph
namespace SpanningGraph
open MyGraph
variable (G : SpanningGraph V)

/-- A *tree* is a connected acyclic graph. -/
@[mk_iff]
structure IsTree : Prop where
  /-- Graph is connected. -/
  protected isConnected : G.Connected
  /-- Graph is acyclic. -/
  protected IsAcyclic : G.IsAcyclic

variable {G}
lemma isTree_coe (hG : G.IsTree) : (G : MyGraph V).IsTree :=
    ⟨hG.isConnected.preconnected, hG.IsAcyclic⟩

lemma IsTree.existsUnique_path (hG : G.IsTree) : ∀ v w,
  ∃! p : G.Walk v w, p.IsPath := by
    intro v w;
    have hG':= isTree_coe hG
    apply isTree_iff_existsUnique_path.1 hG' (by simp) (by simp)


open Walk Path
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
      have h3 := congrArg length (hf' b ((f a).tail.copy h1 rfl) ?_)
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
      have hd : default ∈ G.verts := by simp
      rw [← hf' _ (nil hd) (IsPath.nil hd), length_nil,
          ← hf' _ (.cons h (.nil hd)) ((IsPath.nil hd).cons <| by simpa using h.ne),
          length_cons, length_nil] at h'
      simp [Nat.le_zero, Nat.one_ne_zero] at h'

    rw [← hf' _ (.cons h.symm (f x)) ((cons_isPath_iff _ _).2 ⟨hf _, fun hy => ?contra⟩)]
    · simp only [firstDart_toProd, getVert_cons_succ, getVert_zero, Prod.swap_prod_mk]
    case contra =>
      suffices (f x).takeUntil y hy = .cons h (.nil (h.mem_verts'))by
        rw [← take_spec _ hy] at h'
        simp [this, hf' _ _ ((hf _).dropUntil hy)] at h'
      refine (hG.existsUnique_path _ _).unique ((hf _).takeUntil _) ?_
      simp [h.ne]

-- /-- Every connected graph on `n` vertices has at least `n-1` edges. -/
-- lemma Preconnected.card_vert_le_card_edgeSet_add_one (h : G.Preconnected) :
--     Nat.card V ≤ Nat.card G.edgeSet + 1 := by
--   obtain hV | hV := (finite_or_infinite V).symm
--   · simp
--   have := Fintype.ofFinite
--   obtain ⟨T, hle, hT⟩ := h.exists_isTree_le
--   rw [Nat.card_eq_fintype_card, ← hT.card_edgeFinset, add_le_add_iff_right,
--     Nat.card_eq_fintype_card, ← edgeFinset_card]
--   exact Finset.card_mono <| by simpa

-- lemma isTree_iff_connected_and_card [Finite V] :
--     G.IsTree ↔ G.Preconnected ∧ Nat.card G.edgeSet + 1 = Nat.card V := by
--   have := Fintype.ofFinite V
--   classical
--   refine ⟨fun h ↦ ⟨h.isPreconnected, by simpa using h.card_edgeFinset⟩, fun ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩⟩
--   simp_rw [isAcyclic_iff_forall_adj_isBridge]
--   refine fun x y h ↦ by_contra fun hbr ↦
--     (h₁.connected_delete_edge_of_not_isBridge hbr).card_vert_le_card_edgeSet_add_one.not_lt ?_
--   rw [Nat.card_eq_fintype_card, ← edgeFinset_card, ← h₂, Nat.card_eq_fintype_card,
--     ← edgeFinset_card, add_lt_add_iff_right]
--   exact Finset.card_lt_card <| by simpa [deleteEdges]

end SpanningGraph

/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Path
import Mathlib.Tactic.Linarith

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

lemma _root_.List.Chain'.induction {α : Type*} {R : α → α → Prop} {p : α → Prop} {l : List α}
    (hl : l.Chain' R) (h_head : (lne : l ≠ []) → p (l.head lne))
    (h_inc : ⦃a b : α⦄ → R a b → p a → p b) :
    ∀ x ∈ l, p x := by
  cases l with
  | nil => simp
  | cons a t =>
    simp_all only [ne_eq, not_false_eq_true, List.head_cons, true_implies, List.mem_cons,
    forall_eq_or_imp, implies_true, true_and, List.Chain']
    induction hl with
    | nil =>
      simp
    | @cons a b t hab _ h_ind =>
      simp only [List.mem_cons, forall_eq_or_imp]
      refine ⟨?pb, (fun pb ↦ ?_) ?pb⟩
      · apply h_inc hab
        assumption
      · apply h_ind pb

lemma Dart.ne {G : SimpleGraph V} (d : G.Dart) : d.toProd.1 ≠ d.toProd.2 :=
  fun h ↦ SimpleGraph.irrefl _ (h ▸ d.adj)

lemma Walk.support_head {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.head (by simp) = a := by
  cases p <;> simp

lemma Walk.support_getLast {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.getLast (by simp) = b := by
  induction p
  · simp
  · simpa

lemma Walk.darts_head_fst {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.darts ≠ []) :
    (p.darts.head hp).toProd.1 = a := by
  cases p
  · contradiction
  · simp

lemma _root_.List.getLast_tail {α : Type*} (xs : List α) (h : xs.tail ≠ []) :
    xs.tail.getLast h = xs.getLast (fun x ↦ by simp [x] at h) := by
  cases xs with
  | nil => simp
  | cons x xs =>
    cases xs with
    | nil => simp at h
    | cons y ys => rfl

lemma Walk.darts_getLast_snd {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.darts ≠ []) :
    (p.darts.getLast hp).toProd.2 = b := by
  rw [← List.getLast_map (f := fun x : G.Dart ↦ x.toProd.2)]
  simp_rw [p.map_snd_darts, List.getLast_tail]
  exact p.support_getLast
  simpa

lemma _root_.List.Chain_of_Chain' {α : Type*} {R : α → α → Prop} {l : List α} {v : α}
    (hl : l.Chain' R) (hv : (lne : l ≠ []) → R v (l.head lne)) : l.Chain R v := by
  rw [List.chain_iff_get]
  constructor
  · intro h
    rw [List.get_mk_zero]
    apply hv
  · exact List.chain'_iff_get.mp hl

lemma _root_.List.Chain'.eq_fun {α : Type*} {f : α → α} {l : List α}
    (hl : l.Chain' (fun x y ↦ f x = y)) (hl2 : l ≠ []) :
    f^[l.length - 1] (l.head hl2) = l.getLast hl2 := by
  match l with
  | [] => contradiction
  | a :: l =>
    induction l generalizing a
    · simp
    case cons h t ht =>
      simp only [List.length_cons, add_tsub_cancel_right, List.head_cons, Function.iterate_succ,
        Function.comp_apply, ne_eq, not_false_eq_true, List.getLast_cons]
      rw [← ht]
      · simp only [List.length_cons, add_tsub_cancel_right, List.head_cons]
        congr
        simp at hl
        exact hl.1
      · rw [List.chain'_cons] at hl
        exact hl.2

set_option maxHeartbeats 400000 in
lemma IsAcyclic_of_create (f : V → V) (hf : ∀ x n (_ : 0 < n), f^[n] x = x → f x = x) :
    IsAcyclic (fromRel (· = f ·)) := by classical
  intro a p hp
  let u := p.darts.takeWhile (fun a ↦ f a.toProd.1 = a.toProd.2)
  let d := p.darts.dropWhile (fun a ↦ f a.toProd.1 = a.toProd.2)
  have ud : p.darts = u ++ d := (List.takeWhile_append_dropWhile ..).symm
  have udM : p.edges = u.map Dart.edge ++ d.map Dart.edge :=
    (ud ▸ List.map_append Dart.edge u d :)
  have hu : ∀ a ∈ u, f a.toProd.1 = a.toProd.2 := by
    intros x hx
    apply of_decide_eq_true
    apply List.mem_takeWhile_imp hx
  clear_value u
  have := ud ▸ p.chain'_dartAdj_darts
  have d_chain := this.right_of_append
  rw [List.Chain'.iff_mem] at d_chain
  have u_chain := this.left_of_append
  have dnodup : d.map Dart.edge |>.Nodup := (udM ▸ hp.edges_nodup).of_append_right
  have hd : ∀ a ∈ d, a.toProd.1 = f a.toProd.2 :=
    d_chain.induction
    (fun lne ↦ of_decide_eq_true (by
    have : decide (f (d.head lne).toProd.1 = (d.head lne).toProd.2) = false :=
      List.head_dropWhile_not _ _ lne
    rw [decide_eq_false_iff_not] at this
    rw [decide_eq_true_eq]
    have := (d.head lne).adj
    simp only [fromRel_adj, ne_eq] at this
    tauto
    )) (by
    rintro a b ⟨ha, hb, hab⟩ ha'
    have := b.adj
    simp only [fromRel_adj, ne_eq] at this
    obtain ⟨-, hb' | hb'⟩ := this
    · exact hb'
    unfold DartAdj at hab
    have : a.toProd.1 = b.toProd.2 := by cc
    apply List.inj_on_of_nodup_map at dnodup
    specialize dnodup ha hb _
    · rw [SimpleGraph.dart_edge_eq_iff]
      right
      ext
      simp [this]
      simp [hab]
    exact (b.ne (dnodup ▸ this)).elim
    )
  clear_value d
  match u with
  | [] =>
    rw [List.nil_append] at ud
    clear udM hu this u_chain
    have : List.Chain' (· = f ·) (d.map (·.toProd.2)) := by
      apply List.chain'_map_of_chain' _ _ d_chain
      rintro a b ⟨-, hb, hab⟩
      rw [hab]
      exact hd b hb
    replace : List.Chain' (· = f ·) (a :: d.map (·.toProd.2)) := by
      apply List.Chain_of_Chain' this
      intro lne
      simp
      convert hd _ _
      simp_rw [← ud, Walk.darts_head_fst]
      apply List.head_mem
    replace := List.chain'_reverse.mpr this
    rw [List.reverse_cons] at this
    have headeq : ((List.map (fun x ↦ x.toProd.2) d).reverse ++ [a]).head (by simp) = a := by
      rcases d.eq_nil_or_concat with rfl | ⟨d', b, rfl⟩
      · simp
      · simp only [List.concat_eq_append, List.map_append, List.map_cons, List.map_nil,
        List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.singleton_append, List.cons_append, List.head_cons]
        convert Walk.darts_getLast_snd p (by simp [ud])
        simp [ud]
    have gleq : ((List.map (fun x ↦ x.toProd.2) d).reverse ++ [a]).getLast (by simp) = a := by
      simp
    conv at this =>
      arg 1
      intro a b
      rw [eq_comm]
    have nice := this.eq_fun (by simp)
    rw [headeq, gleq] at nice
    simp only [List.length_append, List.length_reverse, List.length_map, List.length_singleton,
      add_tsub_cancel_right] at nice
    rcases d.eq_nil_or_concat with rfl | ⟨d', b, rfl⟩
    · apply hp.not_nil
      simp [Walk.nil_iff_length_eq, ← Walk.length_darts, ud]
    · apply hf at nice
      · simp at headeq
        specialize hd b
        simp only [List.concat_eq_append, List.mem_append, List.mem_singleton, or_true,
          true_implies] at hd
        apply b.ne
        cc
      · simp
  | v :: u' =>
    rcases d.eq_nil_or_concat with rfl | ⟨d', b, rfl⟩
    · rw [List.append_nil] at ud
      have : List.Chain' (f · = ·) ((v :: u').map (·.toProd.2)) := by
        rw [List.Chain'.iff_mem] at u_chain
        apply List.chain'_map_of_chain' _ _ u_chain
        rintro a b ⟨-, hb, hab⟩
        rw [hab]
        exact hu b hb
      have vf : v.toProd.1 = a := by
        convert Walk.darts_head_fst p (by simp [ud])
        simp [ud]
      replace : List.Chain' (f · = ·) (a :: (v :: u').map (·.toProd.2)) := by
        apply List.Chain_of_Chain' this
        intro lne
        simp [← vf]
        apply hu
        simp
      have gleq : (a :: (v :: u').map (·.toProd.2)).getLast (by simp) = a := by
        simp only [List.map_cons, ne_eq, not_false_eq_true, List.getLast_cons]
        simp_rw [← List.map_cons (·.toProd.2) v, List.getLast_map, ← ud]
        apply darts_getLast_snd
      have nice := this.eq_fun (by simp)
      rw [gleq] at nice
      simp only [List.map_cons, List.length_cons, List.length_map, add_tsub_cancel_right,
        List.head_cons] at nice
      apply hf at nice
      · specialize hu v
        simp only [List.mem_cons, true_or, true_implies] at hu
        apply v.ne
        cc
      · omega
    · have inj := List.inj_on_of_nodup_map hp.edges_nodup (show v ∈ p.darts from by simp [ud])
        (show b ∈ p.darts from by simp [ud])
      have := p.darts_head_fst (by simp [ud])
      simp only [ud, List.concat_eq_append, List.cons_append, List.head_cons] at this
      specialize hu v
      simp only [List.mem_cons, true_or, true_implies] at hu
      have := p.darts_getLast_snd (by simp [ud])
      simp only [ud, List.concat_eq_append, List.cons_append, ne_eq, List.append_eq_nil,
        List.cons_ne_self, and_false, not_false_eq_true, List.getLast_cons,
        List.getLast_append_of_ne_nil, List.getLast_singleton] at this
      specialize hd b
      simp only [List.concat_eq_append, List.mem_append, List.mem_singleton, or_true,
        true_implies] at hd
      specialize inj _
      · rw [dart_edge_eq_iff]
        right
        ext
        · simp only [Dart.symm_toProd, Prod.fst_swap]
          cc
        · simp only [Dart.symm_toProd, Prod.snd_swap]
          cc
      apply v.ne
      cc

end SimpleGraph

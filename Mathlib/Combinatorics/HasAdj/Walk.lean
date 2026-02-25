/-
Copyright (c) 2026 Iván Renison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Iván Renison
-/
module

public import Mathlib.Combinatorics.HasAdj.Basic
public import Mathlib.Data.List.Chain

/-!

-/

@[expose] public section


namespace HasAdj

variable {α : Type*} {Gr : Type*} [HasAdj α Gr]

structure Walk (G : Gr) where
  support : List α
  support_verts (u : α) (hu : u ∈ support) : u ∈ verts G := by aesop
  non_empty_support : support ≠ [] := by aesop
  chainAdj : support.IsChain (Adj G) := by aesop

namespace Walk

variable {G : Gr}

lemma ext_iff {p q : Walk G} : p = q ↔ p.support = q.support := by
  cases p
  cases q
  simp

lemma length_support_pos (p : Walk G) : 0 < p.support.length := by
  rw [← List.ne_nil_iff_length_pos]
  exact p.non_empty_support

/-- The head of a walk is the first vertex in its support. -/
def head (p : Walk G) : α := p.support.head p.non_empty_support

lemma head_mem_verts (p : Walk G) : p.head ∈ verts G := by
  simp [head, p.support_verts]

lemma head_mem_support (p : Walk G) : p.head ∈ p.support :=
  List.head_mem p.non_empty_support

lemma support_nonempty (p : Walk G) : { u | u ∈ p.support }.Nonempty :=
  ⟨p.head, p.head_mem_support⟩

/-- The last vertex of a walk is the last vertex in its support. -/
def last (p : Walk G) : α := p.support.getLast p.non_empty_support

lemma last_mem_verts (p : Walk G) : p.last ∈ verts G := by
  simp [last, p.support_verts]

lemma last_mem_support (p : Walk G) : p.last ∈ p.support :=
  List.getLast_mem p.non_empty_support

/-- The empty walk consisting of a single vertex. -/
def nil {u : α} (hu : u ∈ verts G) : Walk G where
  support := [u]

lemma head_nil {u : α} (hu : u ∈ verts G) : (nil hu).head = u := by simp [nil, head]

lemma last_nil {u : α} (hu : u ∈ verts G) : (nil hu).last = u := by simp [nil, last]

lemma support_nil {u : α} (hu : u ∈ verts G) : (nil hu).support = [u] := rfl

lemma mem_support_nil_iff {u : α} (hu : u ∈ verts G) (v : α) : v ∈ (nil hu).support ↔ v = u := by
  simp [support_nil]

/- Wether a walk is a "nil" walk, i.e. consists of a single vertex. -/
def IsNil (p : Walk G) : Prop := p.support = [p.head]

lemma isNil_nil {u : α} (hu : u ∈ verts G) : IsNil (nil hu) := by
  simp [IsNil, head_nil, support_nil]

lemma IsNil.exist_nil {p : Walk G} (hp : IsNil p) : ∃ (u : α) (hu : u ∈ verts G), p = nil hu := by
  use p.head, p.head_mem_verts
  rw [ext_iff, hp, support_nil]

lemma IsNil.head_eq_last {p : Walk G} (hp : IsNil p) : p.head = p.last := by
  unfold IsNil at hp
  unfold head last
  simp [hp]

lemma IsNil.support_eq_head {p : Walk G} (hp : IsNil p) : p.support = [p.head] := hp

lemma IsNil.support_eq_last {p : Walk G} (hp : IsNil p) : p.support = [p.last] :=
  hp.head_eq_last ▸ hp.support_eq_head

lemma IsNil.mem_support_iff_eq_head {p : Walk G} (hp : IsNil p) (u : α) :
    u ∈ p.support ↔ u = p.head := by
  simp [hp.support_eq_head]

lemma IsNil.mem_support_iff_eq_last {p : Walk G} (hp : IsNil p) (u : α) :
    u ∈ p.support ↔ u = p.last := by
  simp [hp.support_eq_last]

/-- Prepend a vertex to a walk, given an adjacency relation between the new vertex and the head of
  the walk. -/
def cons {u : α} {p : Walk G} (h : Adj G u p.head) : Walk G where
  support := u :: p.support
  support_verts x hx := by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h.left_mem_verts
    · exact p.support_verts x hx
  chainAdj := by
    rw [List.isChain_cons]
    refine ⟨?_, p.chainAdj⟩
    intro x hx
    rw [List.head?_eq_some_head p.non_empty_support, Option.mem_def, Option.some.injEq,
      ← head] at hx
    exact hx ▸ h

lemma head_cons {u : α} {p : Walk G} (h : Adj G u p.head) : (p.cons h).head = u := by
  simp [cons, head]

lemma last_cons {u : α} {p : Walk G} (h : Adj G u p.head) : (p.cons h).last = p.last := by
  simp [cons, last, List.getLast_cons p.non_empty_support]

lemma support_cons {u : α} {p : Walk G} (h : Adj G u p.head) :
    (p.cons h).support = u :: p.support := rfl

lemma support_subset_support_cons {u : α} {p : Walk G} (h : Adj G u p.head) :
    p.support ⊆ (p.cons h).support := by
  rw [support_cons]
  exact p.support.subset_cons_self u

/-- Induction principle for walks.

To prove a property holds for all walks, it suffices to prove:
- It holds for the empty walk `nil hu` for any vertex `u`
- If it holds for a walk `p`, it also holds for `cons h` where `h : Adj G u p.head`
-/
@[elab_as_elim, induction_eliminator]
theorem ind {motive : Walk G → Prop}
    (nil : ∀ (u : α) (hu : u ∈ verts G), motive (nil hu))
    (cons : ∀ (u : α) (p : Walk G) (h : Adj G u p.head), motive p → motive (p.cons h))
    (p : Walk G) : motive p := by
  -- Proof using induction in the support
  have : ∀ (l : List α) (hnonempty : l ≠ []) (hverts : ∀ u ∈ l, u ∈ verts G)
    (hchain : l.IsChain (Adj G)), motive ⟨l, hverts, hnonempty, hchain⟩ := by
    intro l
    induction l with
    | nil =>
      intro h
      exact (h rfl).elim
    | cons u l ihl =>
      intro _ hverts hchain
      by_cases h : l = []
      · subst h
        have hu : u ∈ verts G := hverts u (List.mem_singleton_self u)
        have : (⟨[u], hverts, List.cons_ne_nil u _, hchain⟩ : Walk G) = Walk.nil hu := by
          rw [ext_iff]
          rfl
        rw [this]
        exact nil u hu
      · have hverts' :  ∀ (u : α), u ∈ l → u ∈ verts G :=
          fun x hx ↦ hverts x (List.mem_cons_of_mem u hx)
        have hchain' : l.IsChain (Adj G) := (List.isChain_cons.mp hchain).right
        let p' : Walk G := ⟨l, hverts', h, hchain'⟩
        have hadj : Adj G u p'.head :=
          (List.isChain_cons.mp hchain).left (l.head h) (List.head_mem_head? h)
        have : (⟨u :: l, hverts, by simp, hchain⟩ : Walk G) = Walk.cons hadj := by
          rw [ext_iff]
          rfl
        rw [this]
        apply cons _ p' _ (ihl h hverts' hchain')
  exact this p.support p.non_empty_support p.support_verts p.chainAdj

theorem exists_eq_cons_of_not_nil {p : Walk G} (hp : ¬p.IsNil) :
    ∃ (u : α) (p' : Walk G) (h : Adj G u p'.head), p = cons h := by
  obtain ⟨u, l, hul⟩ := List.ne_nil_iff_exists_cons.mp p.non_empty_support
  let p' : Walk G := {
    support := l
    support_verts x hx := (hul ▸ p.support_verts x) (List.mem_cons_of_mem u hx)
    non_empty_support := by
      simp only [IsNil, head, hul, List.head_cons, List.cons.injEq, true_and] at hp
      exact hp
    chainAdj := (hul ▸ p.chainAdj).of_cons
  }
  have hadj : Adj G u p'.head := by
    simp only [head, p']
    exact (List.isChain_cons.mp (hul ▸ p.chainAdj)).left (l.head p'.non_empty_support)
      (List.head_mem_head? p'.non_empty_support)
  use u, p', hadj
  rw [ext_iff, hul, support_cons]

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def _root_.HasAdj.Adj.toWalk {G : Gr} {u v : α} (h : Adj G u v) : Walk G :=
  (nil h.right_mem_verts).cons h

lemma _root_.HasAdj.Adj.head_toWalk {G : Gr} {u v : α} (h : Adj G u v) : (h.toWalk).head = u := by
  simp [Adj.toWalk, head_cons]

lemma _root_.HasAdj.Adj.last_toWalk {G : Gr} {u v : α} (h : Adj G u v) : (h.toWalk).last = v := by
  simp [Adj.toWalk, last_cons, last_nil]

lemma _root_.HasAdj.Adj.support_toWalk {G : Gr} {u v : α} (h : Adj G u v) :
    (h.toWalk).support = [u, v] := by
  simp [Adj.toWalk, support_cons, support_nil]

lemma _root_.HasAdj.Adj.adj_toWalk_head_last {G : Gr} {u v : α} (h : Adj G u v) :
    Adj G (h.toWalk).head (h.toWalk).last := h

/-- The length of a walk is the number of edges/darts along it. -/
def length (p : Walk G) : ℕ := p.support.length - 1

lemma length_nil {u : α} (hu : u ∈ verts G) : (nil hu).length = 0 := by
  simp [nil, length]

lemma length_cons {u : α} {p : Walk G} (h : Adj G u p.head) : (p.cons h).length = p.length + 1 := by
  simp only [length, cons, List.length_cons, Nat.add_one_sub_one]
  exact (Nat.sub_add_cancel (Nat.one_le_of_lt p.length_support_pos)).symm

lemma _root_.HasAdj.Adj.length_toWalk {G : Gr} {u v : α} (h : Adj G u v) : h.toWalk.length = 1 := by
  simp [Adj.toWalk, length_cons, length_nil]

example (l : List α) (h : l ≠ []) (h' : l.length = 1) : l = [l.head h] := by
  rw [List.head_eq_getElem_zero]
  exact List.eq_getElem_of_length_eq_one l h'

lemma length_eq_zero_iff_isNil {p : Walk G} : p.length = 0 ↔ IsNil p := by
  rw [IsNil, length]
  constructor
  · intro h
    rw [head, List.head_eq_getElem_zero]
    rw [Nat.sub_eq_iff_eq_add' p.length_support_pos] at h
    exact p.support.eq_getElem_of_length_eq_one h
  · intro h
    simp [h]

lemma length_eq_zero_iff_support_eq_singleton {p : Walk G} :
    p.length = 0 ↔ p.support = [p.head] := by
  rw [length_eq_zero_iff_isNil, IsNil]

lemma head_eq_last_of_length_eq_zero {p : Walk G} (hp : p.length = 0) : p.head = p.last :=
  (length_eq_zero_iff_isNil.mp hp).head_eq_last

lemma length_pos_ifff_not_nil {p : Walk G} : 0 < p.length ↔ ¬p.IsNil := by
  grind [length_eq_zero_iff_isNil]

lemma length_eq_one_iff_support_eq_head_last {p : Walk G} :
    p.length = 1 ↔ p.support = [p.head, p.last] := by
  unfold length head last
  simp only [Nat.pred_eq_succ_iff, Nat.zero_add]
  rw [List.length_eq_two']

lemma adj_head_last_of_length_eq_one {p : Walk G} (h : p.length = 1) : Adj G p.head p.last := by
  have := length_eq_one_iff_support_eq_head_last.mp h ▸ p.chainAdj
  simp only [List.isChain_cons_cons, List.IsChain.singleton, and_true] at this
  exact this

end Walk

end HasAdj

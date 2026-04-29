/-
Copyright (c) 2026 Jun Kwon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jun Kwon
-/
module

public import Mathlib.Combinatorics.GraphLike.Walks.Basic
public import Mathlib.Combinatorics.GraphLike.Symm

/-!
# Walks over α × α as dart type

In this file we prove lemmas for walks over `α × α`-valued darts, for `SimpleGraph` and `Digraph`.
Since, in those graphs, the endpoints of a dart completely determine the dart,
we can prove some useful lemmas that characterize `p.darts` in terms of `p.support`.

-/

public section

open HasSourceTarget HasEdge HasInvol SymmDartLike SymmGraphLike GraphLike

variable {V E : Type*} {Gr : Type*} {G : Gr} [HasEdge (V × V) E] [SymmGraphLike V (V × V) E Gr]
  {u v w : V} {p : Walk G u v}

namespace GraphLike

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[expose, match_pattern, reducible]
def Adj.toWalk {G : Gr} {u v : V} (h : Adj G u v) : Walk G u v :=
  Walk.cons (Adj.toStep h) Walk.nil

namespace Walk

theorem adj_of_length_eq_one {u v : V} : ∀ {p : Walk G u v}, p.length = 1 → Adj G u v
  | cons h nil, _ => h.adj

@[simp]
lemma cons_tail_support (p : Walk G u v) : u :: p.support.tail = p.support := by
  cases p <;> simp

theorem mem_darts_iff_infix_support {u' v'} (s : step G u' v') :
    ⟨s.val, s.prop.1⟩ ∈ p.darts ↔ [u', v'] <:+: p.support := by
  refine .trans ⟨fun h ↦ ?_, fun ⟨i, hi, h⟩ ↦ ?_⟩ List.infix_iff_getElem?.symm
  · have ⟨i, hi, h⟩ := List.getElem_of_mem h
    exact ⟨i, by grind, fun j hj ↦ by grind [src_darts_getElem, tgt_darts_getElem]⟩
  · have := h 0
    have := h 1
    obtain rfl := by
      refine Subsingleton.allEq s ⟨p.darts[i]'(by grind), Subtype.coe_prop _, ?_, ?_⟩
      <;> grind [src_darts_getElem, tgt_darts_getElem]
    exact p.darts.getElem_mem (n := i) (by grind)

theorem mem_darts_iff_fst_snd_infix_support (d : GraphLike.darts G) :
    d ∈ p.darts ↔ [d.val.fst, d.val.snd] <:+: p.support :=
  mem_darts_iff_infix_support ⟨d.val, d.prop, rfl, rfl⟩

theorem darts_getElem_eq_fst_snd {u v} {p : Walk G u v} {i : ℕ} (hi : i < p.darts.length) :
    p.darts[i] = (p.support[i]'(by grind), p.support[i + 1]'(by grind)) := by
  match i, p with
  | 0, .cons s_2 p_2 => simp
  | n_1 + 1, .cons s_2 p_2 =>
    simp only [darts_cons, src_eq, tgt_eq, val_step_eq, List.getElem_cons_succ, support_cons]
    exact p_2.darts_getElem_eq_fst_snd _

/-- Construct a walk from a list of vertices where adjacent vertices in the list are also adjacent
in the graph -/
def ofSupport (l : List V) (hne : l ≠ []) (hchain : l.IsChain (Adj G)) :
    Walk G (l.head hne) (l.getLast hne) :=
  match l with
  | [_] => .nil
  | _ :: v :: l => .cons (Adj.toStep hchain.rel)
    <| .ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons

@[simp]
theorem ofSupport_singleton (G : Gr) (v : V) :
    ofSupport [v] ([].cons_ne_nil v) (.singleton v) = .nil (G := G) (u := v) := by
  rfl

@[simp]
theorem ofSupport_cons_cons {l : List V} (hchain : u :: v :: l |>.IsChain (Adj G)) :
    ofSupport (u :: v :: l) ((v :: l).cons_ne_nil u) hchain =
      .cons (Adj.toStep hchain.rel) (.ofSupport (v :: l) (l.cons_ne_nil v) hchain.of_cons) := by
  rfl

@[simp]
theorem support_ofSupport {l : List V} (hne : l ≠ []) (hchain : l.IsChain (Adj G)) :
    (ofSupport l hne hchain).support = l := by
  match l with
  | [_] => rfl
  | _ :: v :: l =>
    simpa using support_ofSupport (l.cons_ne_nil v) hchain.of_cons

@[simp, grind =]
theorem length_ofSupport {l : List V} (hne : l ≠ []) (hchain : l.IsChain (Adj G)) :
    (ofSupport l hne hchain).length = l.length - 1 := by
  grind [support_ofSupport]

end GraphLike.Walk

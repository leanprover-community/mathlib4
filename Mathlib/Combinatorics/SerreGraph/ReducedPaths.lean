/-
Copyright (c) 2024 Siddhartha Gadgil. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddhartha Gadgil
-/
import Mathlib.Combinatorics.SerreGraph.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Parity
/-!
## Reduced paths in graphs

We define reduced paths in graphs, some related operations and prove properties of these operations.

In particular, we define `reduction` of a path, and show that it is homotopic to the original path.
-/
namespace SerreGraph

open EdgePath PathClass

universe u v
variable {V : Type u} {E : Type v} [DecidableEq V] [DecidableEq E]

/--
When `p` is a reduced path from `v` to `w` and `e` is an edge
 from `u` to `v`, `redCons e p` is the reduction of the path `cons e p`.
 The function is defined for paths `p` that may not be reduced,
 but the result need not be reduced if `p` is not reduced.
-/
def redCons {G : SerreGraph V E} {u v w : V} (e: EdgeBetween G u v)
    (p : EdgePath G v w) : EdgePath G u w := by
  match p with
  | nil _ => exact cons e (nil v)
  | cons e' p' =>
      rename_i w' w''
      if c:w'' = u then
        cases c
        if e' = e.bar then exact p'
          else exact cons e (cons e' p')
      else
      exact cons e (cons e' p')

theorem redCons_nil {G : SerreGraph V E} {u v : V}
    (e: EdgeBetween G u v) :  redCons e (nil v) = cons e (nil v) := by
  simp [redCons]

theorem redCons_cons_vertex_neq {G : SerreGraph V E} {u v v' w : V}
    (e: EdgeBetween G u v) (e' : EdgeBetween G v v') (p : EdgePath G v' w) (h : v' ≠ u) : redCons e (cons e' p) = cons e (cons e' p) := by
  simp [redCons, h]

theorem redCons_cons_edge_neq {G : SerreGraph V E} {u v w : V}
    {e: EdgeBetween G u v} {e' : EdgeBetween G v u} (p : EdgePath G u w)
    (h : e' ≠ e.bar) :
    redCons e (cons e' p) = cons e (cons e' p) := by
  simp [redCons, h]

theorem redCons_cons_edge_eq {G : SerreGraph V E} {u v w : V}
    {e: EdgeBetween G u v} {e' : EdgeBetween G v u} (p : EdgePath G u w)
    (h : e' = e.bar) :
    redCons e (cons e' p) = p := by
  simp [redCons, h]

theorem prepend_cases {G : SerreGraph V E} {u v w : V}
    (e: EdgeBetween G u v) (p : EdgePath G v w) :
    (redCons e p) = cons e p ∨ (
    ∃ t : EdgePath G u w, p = cons e.bar t ∧  (redCons e p = t)
    ) := by
  match p with
  | nil _ =>
    simp only [redCons_nil, false_and, exists_false, or_false]
  | cons e' p' =>
    rename_i w' w''
    if c:w'' = u then
      cases c
      if c':e' = e.bar
        then
          simp [redCons_cons_edge_eq p' c']
          simp only [c', or_true]
        else
          simp [redCons_cons_edge_neq p' c']
    else
      simp only [redCons_cons_vertex_neq e e' p' c, cons.injEq, exists_eq_right', true_or]



theorem tail_reducible_of_split {G : SerreGraph V E} {u v w u' v' w': V}
    {e : EdgeBetween G u v} {p : EdgePath G v w}
    {ph: EdgeBetween G u v'}{pt : EdgePath G v' w'}
    {e' : EdgeBetween G w' u'}{p₂ : EdgePath G w' w}
    (hyp : cons e p = (cons ph pt) ++ (cons e' (cons e'.bar p₂))) :
    ¬ reduced p := by
  rw [cons_append] at hyp
  let lhyp := congrArg EdgePath.toList hyp
  simp only [cons_toList, append_toList, EdgeBetween.bar_eq_bar, List.cons.injEq] at lhyp
  have : v' = v := by
    rw [← e.term_eq, ←ph.term_eq]
    symm
    apply congrArg G.τ lhyp.left
  cases this
  have : p = pt ++ (cons e' (cons  e'.bar  p₂)) := by
    apply eq_of_toList_eq
    simp [cons_toList, append_toList]
    exact lhyp.2
  exact not_reduced_of_split this

theorem reduced_singleton {G : SerreGraph V E} {u v : V}
    (e : EdgeBetween G u v) : reduced (cons e (nil v)) := by
  intro p' red'
  let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.property
  cases p₁ with
  | nil _ =>
    rw [nil_append] at eqn
    let leqn := congrArg EdgePath.toList eqn
    simp [cons_toList, nil_toList] at leqn
  | cons h t =>
    rw [cons_append] at eqn
    let leqn := congrArg EdgePath.toList eqn
    simp [cons_toList, nil_toList, append_toList] at leqn

theorem reduced_nil {G : SerreGraph V E} {v : V} :
    reduced (nil v : EdgePath G v v) := by
  intro p' red'
  let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.property
  cases p₁ with
  | nil _ =>
    rw [nil_append] at eqn
    let leqn := congrArg EdgePath.toList eqn
    simp [cons_toList, nil_toList] at leqn
  | cons h t =>
    rw [cons_append] at eqn
    let leqn := congrArg EdgePath.toList eqn
    simp [cons_toList, nil_toList, append_toList] at leqn


theorem reduced_redCons (G : SerreGraph V E) {u v w : V}
    (e: EdgeBetween G u v) (p : EdgePath G v w) (hyp : reduced p):
    reduced (redCons e p) := by
  match p with
  | nil _ =>
    simp [redCons_nil]
    apply reduced_singleton
  | cons e' p' =>
    rename_i w' w''
    if c:w'' = u then
      cases c
      if c':e' = e.bar
        then
          simp [redCons_cons_edge_eq p' c']
          intro p'' red'
          let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.property
          rw [←eqn, ← cons_append] at hyp
          let red := hyp <| cons e' p₁ ++ p₂
          apply red
          apply Reduction.step
        else
          simp [redCons_cons_edge_neq p' c']
          intro p'' red'
          let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.property
          match p₁ with
          | nil _ =>
            rw [nil_append] at eqn
            let leqn := congrArg EdgePath.toList eqn
            simp [cons_toList, nil_toList, append_toList] at leqn
            rename_i e''
            have : e' = e''.bar := by
              ext
              rw [EdgeBetween.bar_eq_bar]
              rw [← leqn.1, leqn.2.1]
            contradiction
          | cons ph pt =>
            symm at eqn
            let tred : ¬ reduced (cons e' p') :=
              tail_reducible_of_split eqn
            contradiction
    else
      simp [redCons_cons_vertex_neq e e' p' c]
      intro p'' red'
      let ⟨u, u', e, p₁, p₂, eqn⟩   := red'.property
      match p₁ with
          | nil _ =>
            rw [nil_append] at eqn
            let leqn := congrArg EdgePath.toList eqn
            simp [cons_toList, nil_toList, append_toList] at leqn
            rename_i u'' e''
            apply c
            rw [← e.init_eq, ← e'.term_eq, ← G.ι_bar, ← leqn.2.1, bar_bar]
          | cons ph pt =>
            symm at eqn
            let tred : ¬ reduced (cons e' p') :=
              tail_reducible_of_split eqn
            contradiction

theorem cancelling_steps_redCons {G : SerreGraph V E} {u v w : V}
    (e: EdgeBetween G u v) (p : EdgePath G v w) (hyp : reduced p):
    redCons e.bar (redCons e p) = p := by
  cases prepend_cases e p with
  | inl h =>
      rw [h]
      apply redCons_cons_edge_eq
      simp [bar_bar]
  | inr h =>
      let ⟨t, h₁, h₂⟩ := h
      rw[h₂, h₁]
      cases prepend_cases e.bar t with
      | inl h' =>
        assumption
      | inr h' =>
        let ⟨t', h₁', h₂'⟩ := h'
        rw [h₂', h₁']
        rw [h₁, h₁'] at hyp
        simp [bar_bar] at *
        have split :
                  cons e.bar (cons e t') =
                    (nil v : EdgePath G v v) ++
                      cons e.bar (cons e.bar.bar t') := by
                    simp [nil_append]
        have :¬ reduced (cons e.bar (cons e t')) := by
          apply not_reduced_of_split split
        contradiction

theorem redCons_eq_cons_of_reduced {G : SerreGraph V E} {u v w : V}
    (e: EdgeBetween G u v) (p : EdgePath G v w) (hyp : reduced (cons e p)):
    redCons e p = cons e p := by
  cases prepend_cases e p with
  | inl h =>
      rw [h]
  | inr h =>
      let ⟨t, h₁, h₂⟩ := h
      rw [h₁] at hyp
      have split :
        cons e (cons e.bar t) =
          (nil u : EdgePath G u u) ++
            cons e (cons e.bar t) := by
          simp [nil_append]
      have :¬ reduced (cons e (cons e.bar t)) := by
              apply not_reduced_of_split split
      contradiction

theorem cons_homotopic_redCons {G : SerreGraph V E} {u v w : V}
    (e: EdgeBetween G u v) (p : EdgePath G v w):
    [[ cons  e p ]] = [[ redCons e p ]] := by
  cases prepend_cases e p with
  | inl h =>
      rw [h]
  | inr h =>
      let ⟨t, h₁, h₂⟩ := h
      rw [h₂, h₁]
      apply Quot.sound
      have split :
        cons e (cons e.bar t) =
          (nil u : EdgePath G u u) ++
            cons e (cons e.bar t) := by
          simp [nil_append]
      rw [split]
      apply Reduction.step

/--
The reduction of a path, defined by induction on the path.
-/
def reduction {G: SerreGraph V E} {v w : V} (p : EdgePath G v w) :
    EdgePath G v w :=
  match p with
  | nil _ => nil v
  | cons e p => redCons e (reduction p)

theorem reduction_nil {G: SerreGraph V E} {v : V} :
    reduction (nil v : EdgePath G v v) = nil v := by
  simp [reduction]

theorem reduction_cons {G: SerreGraph V E} {v w u : V}
    (e: EdgeBetween G v w) (p : EdgePath G w u) :
  reduction (cons e p) = redCons e (reduction p) := by
  simp [reduction]

theorem reduction_reduced {G: SerreGraph V E} {v w : V} (p : EdgePath G v w) :
    reduced (reduction p) := by
  induction p with
  | nil _ =>
    simp [reduction_nil, reduced_nil]
  | cons e p ih =>
    apply reduced_redCons
    assumption

theorem reduction_eq_self_of_reduced {G: SerreGraph V E} {v w : V} (p : EdgePath G v w) (hyp : reduced p) :
    reduction p = p := by
  induction p with
  | nil _ =>
    simp [reduction_nil]
  | cons e p ih =>
    rw [reduction_cons]
    have teq : reduction p = p := by
      apply ih
      apply tail_reduced
      assumption
    rw [teq]
    apply redCons_eq_cons_of_reduced
    assumption

theorem reduction_homotopic_self {G: SerreGraph V E} {v w : V}
    (p : EdgePath G v w)  :
    [[ reduction p ]] = [[ p ]] := by
  induction p with
  | nil _ =>
    simp [reduction_nil]
  | cons e p ih =>
    simp [reduction_cons, ←cons_homotopic_redCons]
    apply cons_equiv_of_equiv
    assumption

theorem redCons_parity_neq {G : SerreGraph V E} {u v w : V}
    (e: EdgeBetween G u v) (p : EdgePath G v w) :
    Even ((redCons e p).toList.length) ↔ ¬ Even (p.toList.length) := by
  cases prepend_cases e p with
  | inl h =>
    rw [h]
    simp only [cons_toList, List.length_cons]
    apply Nat.even_add_one
  | inr h =>
    let ⟨t, h₁, h₂⟩ := h
    rw [h₂, h₁]
    simp  [cons_toList, List.length_cons, Nat.even_add_one]

/--
Reduction of a path obtained by concatenating an edge to a reduced path.
The function is defined for paths `p` that may not be reduced,
but the result need not be reduced if `p` is not reduced.
-/
def reducedConcat {G : SerreGraph V E} {v w u : V}
    (p : EdgePath G v w) (e: EdgeBetween G w u) :
  EdgePath G v u :=
  reverse <| redCons e.bar (reverse p)

infixl:65 ":+" => reducedConcat

theorem reducedConcat_reduced {G : SerreGraph V E} {v w u : V}
    (p : EdgePath G v w) (e: EdgeBetween G w u) (hyp : reduced p) :
  reduced (p :+ e) := by
  simp only [reducedConcat]
  apply reverse_reduced
  apply reduced_redCons
  apply reverse_reduced
  apply hyp

theorem reducedConcat_cancel_pair {G : SerreGraph V E} {v w u : V}
    (p : EdgePath G v w) (e: EdgeBetween G w u) (hyp : reduced p) :
    p :+ e :+ e.bar = p := by
  have hyp' :=  reverse_reduced p hyp
  simp only [reducedConcat, EdgeBetween.bar_bar, reverse_reverse]
  let lm :
    redCons e.bar.bar (redCons (EdgeBetween.bar e) (reverse p))
      = reverse p :=
    by
      apply cancelling_steps_redCons
      assumption
  simp at lm
  rw [lm, reverse_reverse]

theorem concat_parity {G : SerreGraph V E} {v w u : V}
    (p : EdgePath G v w) (e: EdgeBetween G w u)  :
    Even ((p :+ e).toList.length) ↔ ¬ Even (p.toList.length) := by
  simp  [reducedConcat, reverse_toList]
  rw [redCons_parity_neq e.bar (reverse p)]
  simp [reverse_toList]

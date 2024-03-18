/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.List.Rotate

#align_import combinatorics.simple_graph.connectivity from "leanprover-community/mathlib"@"b99e2d58a5e6861833fa8de11e51a81144258db4"

/-!
# Walks in graphs

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be thought of
equally well as a sequence of directed edges.

Some definitions and theorems have inspiration from multigraph counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions `Walk.nil'` and `Walk.cons'`)
-/

namespace SimpleGraph

variable {V V' V'' : Type*} (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')
  {u v w u' v' w' : V}

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `Walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type*
  | nil {u : V} : Walk u u
  | cons {u v w : V} (h : G.Adj u v) (p : Walk v w) : Walk u w
  deriving DecidableEq
#align simple_graph.walk SimpleGraph.Walk

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited (v : V) : Inhabited (G.Walk v v) := ⟨Walk.nil⟩
#align simple_graph.walk.inhabited SimpleGraph.Walk.instInhabited

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil
#align simple_graph.adj.to_walk SimpleGraph.Adj.toWalk

namespace Walk

variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : V) : G.Walk u u := Walk.nil
#align simple_graph.walk.nil' SimpleGraph.Walk.nil'

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w := Walk.cons h p
#align simple_graph.walk.cons' SimpleGraph.Walk.cons'

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p
#align simple_graph.walk.copy SimpleGraph.Walk.copy

@[simp]
theorem copy_rfl_rfl (p : G.Walk u v) : p.copy rfl rfl = p := rfl
#align simple_graph.walk.copy_rfl_rfl SimpleGraph.Walk.copy_rfl_rfl

@[simp]
theorem copy_copy (p : G.Walk u u') (hu : u = v) (hv : u' = v') (hu' : v = w) (hv' : v' = w') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl
#align simple_graph.walk.copy_copy SimpleGraph.Walk.copy_copy

@[simp]
theorem copy_nil (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = Walk.nil := by
  subst_vars
  rfl
#align simple_graph.walk.copy_nil SimpleGraph.Walk.copy_nil

theorem copy_cons (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl
#align simple_graph.walk.copy_cons SimpleGraph.Walk.copy_cons

@[simp]
theorem cons_copy (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    Walk.cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl
#align simple_graph.walk.cons_copy SimpleGraph.Walk.cons_copy

theorem exists_eq_cons_of_ne (hne : u ≠ v) :
    ∀ (p : G.Walk u v), ∃ (w : V) (h : G.Adj u w) (p' : G.Walk w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩
#align simple_graph.walk.exists_eq_cons_of_ne SimpleGraph.Walk.exists_eq_cons_of_ne

/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ
#align simple_graph.walk.length SimpleGraph.Walk.length

/-- The concatenation of two compatible walks. -/
@[trans]
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)
#align simple_graph.walk.append SimpleGraph.Walk.append

/-- The reversed version of `SimpleGraph.Walk.cons`, concatenating an edge to
the end of a walk. -/
def concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w := p.append (cons h nil)
#align simple_graph.walk.concat SimpleGraph.Walk.concat

theorem concat_eq_append {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    p.concat h = p.append (cons h nil) := rfl
#align simple_graph.walk.concat_eq_append SimpleGraph.Walk.concat_eq_append

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux {u v w : V} : G.Walk u v → G.Walk u w → G.Walk v w
  | nil, q => q
  | cons h p, q => Walk.reverseAux p (cons (G.symm h) q)
#align simple_graph.walk.reverse_aux SimpleGraph.Walk.reverseAux

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u := w.reverseAux nil
#align simple_graph.walk.reverse SimpleGraph.Walk.reverse

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the walk's endpoint. -/
def getVert {u v : V} : G.Walk u v → ℕ → V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n
#align simple_graph.walk.get_vert SimpleGraph.Walk.getVert

@[simp]
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by cases w <;> rfl
#align simple_graph.walk.get_vert_zero SimpleGraph.Walk.getVert_zero

theorem getVert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) :
    w.getVert i = v := by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)
#align simple_graph.walk.get_vert_of_length_le SimpleGraph.Walk.getVert_of_length_le

@[simp]
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_length_le rfl.le
#align simple_graph.walk.get_vert_length SimpleGraph.Walk.getVert_length

theorem adj_getVert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)
#align simple_graph.walk.adj_get_vert_succ SimpleGraph.Walk.adj_getVert_succ

@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) := rfl
#align simple_graph.walk.cons_append SimpleGraph.Walk.cons_append

@[simp]
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p := rfl
#align simple_graph.walk.cons_nil_append SimpleGraph.Walk.cons_nil_append

@[simp]
theorem append_nil {u v : V} (p : G.Walk u v) : p.append nil = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => rw [cons_append, ih]
#align simple_graph.walk.append_nil SimpleGraph.Walk.append_nil

@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl
#align simple_graph.walk.nil_append SimpleGraph.Walk.nil_append

theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    p.append (q.append r) = (p.append q).append r := by
  induction p with
  | nil => rfl
  | cons h p' ih =>
    dsimp only [append]
    rw [ih]
#align simple_graph.walk.append_assoc SimpleGraph.Walk.append_assoc

@[simp]
theorem append_copy_copy (p : G.Walk u v) (q : G.Walk v w)
    (hu : u = u') (hv : v = v') (hw : w = w') :
    (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by
  subst_vars
  rfl
#align simple_graph.walk.append_copy_copy SimpleGraph.Walk.append_copy_copy

theorem concat_nil {u v : V} (h : G.Adj u v) : nil.concat h = cons h nil := rfl
#align simple_graph.walk.concat_nil SimpleGraph.Walk.concat_nil

@[simp]
theorem concat_cons {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x) :
    (cons h p).concat h' = cons h (p.concat h') := rfl
#align simple_graph.walk.concat_cons SimpleGraph.Walk.concat_cons

theorem append_concat {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x) :
    p.append (q.concat h) = (p.append q).concat h := append_assoc _ _ _
#align simple_graph.walk.append_concat SimpleGraph.Walk.append_concat

theorem concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x) :
    (p.concat h).append q = p.append (cons h q) := by
  rw [concat_eq_append, ← append_assoc, cons_nil_append]
#align simple_graph.walk.concat_append SimpleGraph.Walk.concat_append

/-- A non-trivial `cons` walk is representable as a `concat` walk. -/
theorem exists_cons_eq_concat {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    ∃ (x : V) (q : G.Walk u x) (h' : G.Adj x w), cons h p = q.concat h' := by
  induction p generalizing u with
  | nil => exact ⟨_, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨y, q, h'', hc⟩ := ih h'
    refine' ⟨y, cons h q, h'', _⟩
    rw [concat_cons, hc]
#align simple_graph.walk.exists_cons_eq_concat SimpleGraph.Walk.exists_cons_eq_concat

/-- A non-trivial `concat` walk is representable as a `cons` walk. -/
theorem exists_concat_eq_cons {u v w : V} :
    ∀ (p : G.Walk u v) (h : G.Adj v w),
      ∃ (x : V) (h' : G.Adj u x) (q : G.Walk x w), p.concat h = cons h' q
  | nil, h => ⟨_, h, nil, rfl⟩
  | cons h' p, h => ⟨_, h', Walk.concat p h, concat_cons _ _ _⟩
#align simple_graph.walk.exists_concat_eq_cons SimpleGraph.Walk.exists_concat_eq_cons

@[simp]
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil := rfl
#align simple_graph.walk.reverse_nil SimpleGraph.Walk.reverse_nil

theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons (G.symm h) nil :=
  rfl
#align simple_graph.walk.reverse_singleton SimpleGraph.Walk.reverse_singleton

@[simp]
theorem cons_reverseAux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons (G.symm h) q) := rfl
#align simple_graph.walk.cons_reverse_aux SimpleGraph.Walk.cons_reverseAux

@[simp]
protected theorem append_reverseAux {u v w x : V}
    (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x) :
    (p.append q).reverseAux r = q.reverseAux (p.reverseAux r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons (G.symm h) r)
#align simple_graph.walk.append_reverse_aux SimpleGraph.Walk.append_reverseAux

@[simp]
protected theorem reverseAux_append {u v w x : V}
    (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons (G.symm h) q)]
#align simple_graph.walk.reverse_aux_append SimpleGraph.Walk.reverseAux_append

protected theorem reverseAux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by simp [reverse]
#align simple_graph.walk.reverse_aux_eq_reverse_append SimpleGraph.Walk.reverseAux_eq_reverse_append

@[simp]
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) := by simp [reverse]
#align simple_graph.walk.reverse_cons SimpleGraph.Walk.reverse_cons

@[simp]
theorem reverse_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu := by
  subst_vars
  rfl
#align simple_graph.walk.reverse_copy SimpleGraph.Walk.reverse_copy

@[simp]
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by simp [reverse]
#align simple_graph.walk.reverse_append SimpleGraph.Walk.reverse_append

@[simp]
theorem reverse_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).reverse = cons (G.symm h) p.reverse := by simp [concat_eq_append]
#align simple_graph.walk.reverse_concat SimpleGraph.Walk.reverse_concat

@[simp]
theorem reverse_reverse {u v : V} (p : G.Walk u v) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
#align simple_graph.walk.reverse_reverse SimpleGraph.Walk.reverse_reverse

@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 := rfl
#align simple_graph.walk.length_nil SimpleGraph.Walk.length_nil

@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 := rfl
#align simple_graph.walk.length_cons SimpleGraph.Walk.length_cons

@[simp]
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl
#align simple_graph.walk.length_copy SimpleGraph.Walk.length_copy

@[simp]
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih, add_comm, add_left_comm, add_assoc]
#align simple_graph.walk.length_append SimpleGraph.Walk.length_append

@[simp]
theorem length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = p.length + 1 := length_append _ _
#align simple_graph.walk.length_concat SimpleGraph.Walk.length_concat

@[simp]
protected theorem length_reverseAux {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    (p.reverseAux q).length = p.length + q.length := by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.add_succ, Nat.succ_add]
#align simple_graph.walk.length_reverse_aux SimpleGraph.Walk.length_reverseAux

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]
#align simple_graph.walk.length_reverse SimpleGraph.Walk.length_reverse

theorem eq_of_length_eq_zero {u v : V} : ∀ {p : G.Walk u v}, p.length = 0 → u = v
  | nil, _ => rfl
#align simple_graph.walk.eq_of_length_eq_zero SimpleGraph.Walk.eq_of_length_eq_zero

@[simp]
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v := by
  constructor
  · rintro ⟨p, hp⟩
    exact eq_of_length_eq_zero hp
  · rintro rfl
    exact ⟨nil, rfl⟩
#align simple_graph.walk.exists_length_eq_zero_iff SimpleGraph.Walk.exists_length_eq_zero_iff

@[simp]
theorem length_eq_zero_iff {u : V} {p : G.Walk u u} : p.length = 0 ↔ p = nil := by cases p <;> simp
#align simple_graph.walk.length_eq_zero_iff SimpleGraph.Walk.length_eq_zero_iff

section ConcatRec

variable {motive : ∀ u v : V, G.Walk u v → Sort*} (Hnil : ∀ {u : V}, motive u u nil)
  (Hconcat : ∀ {u v w : V} (p : G.Walk u v) (h : G.Adj v w), motive u v p → motive u w (p.concat h))

/-- Auxiliary definition for `SimpleGraph.Walk.concatRec` -/
def concatRecAux {u v : V} : (p : G.Walk u v) → motive v u p.reverse
  | nil => Hnil
  | cons h p => reverse_cons h p ▸ Hconcat p.reverse h.symm (concatRecAux p)
#align simple_graph.walk.concat_rec_aux SimpleGraph.Walk.concatRecAux

/-- Recursor on walks by inducting on `SimpleGraph.Walk.concat`.

This is inducting from the opposite end of the walk compared
to `SimpleGraph.Walk.rec`, which inducts on `SimpleGraph.Walk.cons`. -/
@[elab_as_elim]
def concatRec {u v : V} (p : G.Walk u v) : motive u v p :=
  reverse_reverse p ▸ concatRecAux @Hnil @Hconcat p.reverse
#align simple_graph.walk.concat_rec SimpleGraph.Walk.concatRec

@[simp]
theorem concatRec_nil (u : V) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (nil : G.Walk u u) = Hnil := rfl
#align simple_graph.walk.concat_rec_nil SimpleGraph.Walk.concatRec_nil

@[simp]
theorem concatRec_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (p.concat h) =
      Hconcat p h (concatRec @Hnil @Hconcat p) := by
  simp only [concatRec]
  apply eq_of_heq
  apply rec_heq_of_heq
  trans concatRecAux @Hnil @Hconcat (cons h.symm p.reverse)
  · congr
    simp
  · rw [concatRecAux, rec_heq_iff_heq]
    congr <;> simp [heq_rec_iff_heq]
#align simple_graph.walk.concat_rec_concat SimpleGraph.Walk.concatRec_concat

end ConcatRec

theorem concat_ne_nil {u v : V} (p : G.Walk u v) (h : G.Adj v u) : p.concat h ≠ nil := by
  cases p <;> simp [concat]
#align simple_graph.walk.concat_ne_nil SimpleGraph.Walk.concat_ne_nil

theorem concat_inj {u v v' w : V} {p : G.Walk u v} {h : G.Adj v w} {p' : G.Walk u v'}
    {h' : G.Adj v' w} (he : p.concat h = p'.concat h') : ∃ hv : v = v', p.copy rfl hv = p' := by
  induction p with
  | nil =>
    cases p'
    · exact ⟨rfl, rfl⟩
    · exfalso
      simp only [concat_nil, concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      simp only [heq_iff_eq] at he
      exact concat_ne_nil _ _ he.symm
  | cons _ _ ih =>
    rw [concat_cons] at he
    cases p'
    · exfalso
      simp only [concat_nil, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      rw [heq_iff_eq] at he
      exact concat_ne_nil _ _ he
    · rw [concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      rw [heq_iff_eq] at he
      obtain ⟨rfl, rfl⟩ := ih he
      exact ⟨rfl, rfl⟩
#align simple_graph.walk.concat_inj SimpleGraph.Walk.concat_inj

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support
#align simple_graph.walk.support SimpleGraph.Walk.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts
#align simple_graph.walk.darts SimpleGraph.Walk.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge
#align simple_graph.walk.edges SimpleGraph.Walk.edges

@[simp]
theorem support_nil {u : V} : (nil : G.Walk u u).support = [u] := rfl
#align simple_graph.walk.support_nil SimpleGraph.Walk.support_nil

@[simp]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u :: p.support := rfl
#align simple_graph.walk.support_cons SimpleGraph.Walk.support_cons

@[simp]
theorem support_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).support = p.support.concat w := by
  induction p <;> simp [*, concat_nil]
#align simple_graph.walk.support_concat SimpleGraph.Walk.support_concat

@[simp]
theorem support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by
  subst_vars
  rfl
#align simple_graph.walk.support_copy SimpleGraph.Walk.support_copy

theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support ++ p'.support.tail := by
  induction p <;> cases p' <;> simp [*]
#align simple_graph.walk.support_append SimpleGraph.Walk.support_append

@[simp]
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.support = p.support.reverse := by
  induction p <;> simp [support_append, *]
#align simple_graph.walk.support_reverse SimpleGraph.Walk.support_reverse

@[simp]
theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.support ≠ [] := by cases p <;> simp
#align simple_graph.walk.support_ne_nil SimpleGraph.Walk.support_ne_nil

theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]
#align simple_graph.walk.tail_support_append SimpleGraph.Walk.tail_support_append

theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp
#align simple_graph.walk.support_eq_cons SimpleGraph.Walk.support_eq_cons

@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp
#align simple_graph.walk.start_mem_support SimpleGraph.Walk.start_mem_support

@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]
#align simple_graph.walk.end_mem_support SimpleGraph.Walk.end_mem_support

@[simp]
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩
#align simple_graph.walk.support_nonempty SimpleGraph.Walk.support_nonempty

theorem mem_support_iff {u v w : V} (p : G.Walk u v) : w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail :=
  by cases p <;> simp
#align simple_graph.walk.mem_support_iff SimpleGraph.Walk.mem_support_iff

theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).support ↔ u = v := by simp
#align simple_graph.walk.mem_support_nil_iff SimpleGraph.Walk.mem_support_nil_iff

@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
  rw [tail_support_append, List.mem_append]
#align simple_graph.walk.mem_tail_support_append_iff SimpleGraph.Walk.mem_tail_support_append_iff

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp
#align simple_graph.walk.end_mem_tail_support_of_ne SimpleGraph.Walk.end_mem_tail_support_of_ne

@[simp, nolint unusedHavesSuffices]
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support := by
  simp only [mem_support_iff, mem_tail_support_append_iff]
  obtain rfl | h := eq_or_ne t v <;> obtain rfl | h' := eq_or_ne t u <;>
    -- this `have` triggers the unusedHavesSuffices linter:
    (try have := h'.symm) <;> simp [*]
#align simple_graph.walk.mem_support_append_iff SimpleGraph.Walk.mem_support_append_iff

@[simp]
theorem subset_support_append_left {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
  simp only [Walk.support_append, List.subset_append_left]
#align simple_graph.walk.subset_support_append_left SimpleGraph.Walk.subset_support_append_left

@[simp]
theorem subset_support_append_right {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support := by
  intro h
  simp (config := { contextual := true }) only [mem_support_append_iff, or_true_iff, imp_true_iff]
#align simple_graph.walk.subset_support_append_right SimpleGraph.Walk.subset_support_append_right

theorem coe_support {u v : V} (p : G.Walk u v) : (p.support : Multiset V) = {u} + p.support.tail :=
  by cases p <;> rfl
#align simple_graph.walk.coe_support SimpleGraph.Walk.coe_support

theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]
#align simple_graph.walk.coe_support_append SimpleGraph.Walk.coe_support_append

theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = p.support + p'.support - {v} := by
  rw [support_append, ← Multiset.coe_add]
  simp only [coe_support]
  rw [add_comm ({v} : Multiset V)]
  simp only [← add_assoc, add_tsub_cancel_right]
#align simple_graph.walk.coe_support_append' SimpleGraph.Walk.coe_support_append'

theorem chain_adj_support {u v w : V} (h : G.Adj u v) :
    ∀ (p : G.Walk v w), List.Chain G.Adj u p.support
  | nil => List.Chain.cons h List.Chain.nil
  | cons h' p => List.Chain.cons h (chain_adj_support h' p)
#align simple_graph.walk.chain_adj_support SimpleGraph.Walk.chain_adj_support

theorem chain'_adj_support {u v : V} : ∀ (p : G.Walk u v), List.Chain' G.Adj p.support
  | nil => List.Chain.nil
  | cons h p => chain_adj_support h p
#align simple_graph.walk.chain'_adj_support SimpleGraph.Walk.chain'_adj_support

theorem chain_dartAdj_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) :
    List.Chain G.DartAdj d p.darts := by
  induction p generalizing d with
  | nil => exact List.Chain.nil
  -- Porting note: needed to defer `h` and `rfl` to help elaboration
  | cons h' p ih => exact List.Chain.cons (by exact h) (ih (by rfl))
#align simple_graph.walk.chain_dart_adj_darts SimpleGraph.Walk.chain_dartAdj_darts

theorem chain'_dartAdj_darts {u v : V} : ∀ (p : G.Walk u v), List.Chain' G.DartAdj p.darts
  | nil => trivial
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => chain_dartAdj_darts (by rfl) p
#align simple_graph.walk.chain'_dart_adj_darts SimpleGraph.Walk.chain'_dartAdj_darts

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
theorem edges_subset_edgeSet {u v : V} :
    ∀ (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
  | cons h' p', e, h => by
    cases h
    · exact h'
    next h' => exact edges_subset_edgeSet p' h'
#align simple_graph.walk.edges_subset_edge_set SimpleGraph.Walk.edges_subset_edgeSet

theorem adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y :=
  edges_subset_edgeSet p h
#align simple_graph.walk.adj_of_mem_edges SimpleGraph.Walk.adj_of_mem_edges

@[simp]
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] := rfl
#align simple_graph.walk.darts_nil SimpleGraph.Walk.darts_nil

@[simp]
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl
#align simple_graph.walk.darts_cons SimpleGraph.Walk.darts_cons

@[simp]
theorem darts_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩ := by
  induction p <;> simp [*, concat_nil]
#align simple_graph.walk.darts_concat SimpleGraph.Walk.darts_concat

@[simp]
theorem darts_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).darts = p.darts := by
  subst_vars
  rfl
#align simple_graph.walk.darts_copy SimpleGraph.Walk.darts_copy

@[simp]
theorem darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').darts = p.darts ++ p'.darts := by
  induction p <;> simp [*]
#align simple_graph.walk.darts_append SimpleGraph.Walk.darts_append

@[simp]
theorem darts_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.darts = (p.darts.map Dart.symm).reverse := by
  induction p <;> simp [*, Sym2.eq_swap]
#align simple_graph.walk.darts_reverse SimpleGraph.Walk.darts_reverse

theorem mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} :
    d ∈ p.reverse.darts ↔ d.symm ∈ p.darts := by simp
#align simple_graph.walk.mem_darts_reverse SimpleGraph.Walk.mem_darts_reverse

theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u :: p.darts.map (·.snd)) = p.support := by
  induction p <;> simp! [*]
#align simple_graph.walk.cons_map_snd_darts SimpleGraph.Walk.cons_map_snd_darts

theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)
#align simple_graph.walk.map_snd_darts SimpleGraph.Walk.map_snd_darts

theorem map_fst_darts_append {u v : V} (p : G.Walk u v) :
    p.darts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp! [*]
#align simple_graph.walk.map_fst_darts_append SimpleGraph.Walk.map_fst_darts_append

theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_darts_append p)
#align simple_graph.walk.map_fst_darts SimpleGraph.Walk.map_fst_darts

@[simp]
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] := rfl
#align simple_graph.walk.edges_nil SimpleGraph.Walk.edges_nil

@[simp]
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edges = s(u, v) :: p.edges := rfl
#align simple_graph.walk.edges_cons SimpleGraph.Walk.edges_cons

@[simp]
theorem edges_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edges = p.edges.concat s(v, w) := by simp [edges]
#align simple_graph.walk.edges_concat SimpleGraph.Walk.edges_concat

@[simp]
theorem edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by
  subst_vars
  rfl
#align simple_graph.walk.edges_copy SimpleGraph.Walk.edges_copy

@[simp]
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').edges = p.edges ++ p'.edges := by simp [edges]
#align simple_graph.walk.edges_append SimpleGraph.Walk.edges_append

@[simp]
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  simp [edges, List.map_reverse]
#align simple_graph.walk.edges_reverse SimpleGraph.Walk.edges_reverse

@[simp]
theorem length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]
#align simple_graph.walk.length_support SimpleGraph.Walk.length_support

@[simp]
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]
#align simple_graph.walk.length_darts SimpleGraph.Walk.length_darts

@[simp]
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by simp [edges]
#align simple_graph.walk.length_edges SimpleGraph.Walk.length_edges

theorem dart_fst_mem_support_of_mem_darts {u v : V} :
    ∀ (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.fst ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with (rfl | hd)
    · exact Or.inl rfl
    · exact Or.inr (dart_fst_mem_support_of_mem_darts _ hd)
#align simple_graph.walk.dart_fst_mem_support_of_mem_darts SimpleGraph.Walk.dart_fst_mem_support_of_mem_darts

theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart}
    (h : d ∈ p.darts) : d.snd ∈ p.support := by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm ∈ p.reverse.darts)
#align simple_graph.walk.dart_snd_mem_support_of_mem_darts SimpleGraph.Walk.dart_snd_mem_support_of_mem_darts

theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    t ∈ p.support := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd
#align simple_graph.walk.fst_mem_support_of_mem_edges SimpleGraph.Walk.fst_mem_support_of_mem_edges

theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    u ∈ p.support := by
  rw [Sym2.eq_swap] at he
  exact p.fst_mem_support_of_mem_edges he
#align simple_graph.walk.snd_mem_support_of_mem_edges SimpleGraph.Walk.snd_mem_support_of_mem_edges

theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨fun h' => h.1 (dart_fst_mem_support_of_mem_darts p' h'), ih h.2⟩
#align simple_graph.walk.darts_nodup_of_support_nodup SimpleGraph.Walk.darts_nodup_of_support_nodup

theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.edges.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [edges_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨fun h' => h.1 (fst_mem_support_of_mem_edges p' h'), ih h.2⟩
#align simple_graph.walk.edges_nodup_of_support_nodup SimpleGraph.Walk.edges_nodup_of_support_nodup

/-- Predicate for the empty walk.

Solves the dependent type problem where `p = G.Walk.nil` typechecks
only if `p` has defeq endpoints. -/
inductive Nil : {v w : V} → G.Walk v w → Prop
  | nil {u : V} : Nil (nil : G.Walk u u)

@[simp] lemma nil_nil : (nil : G.Walk u u).Nil := Nil.nil

@[simp] lemma not_nil_cons {h : G.Adj u v} {p : G.Walk v w} : ¬(cons h p).Nil := nofun

instance (p : G.Walk v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq {p : G.Walk v w} : p.Nil → v = w | .nil => rfl

lemma not_nil_of_ne {p : G.Walk v w} : v ≠ w → ¬p.Nil := mt Nil.eq

lemma nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

lemma nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0 := by
  cases p <;> simp

lemma not_nil_iff {p : G.Walk v w} :
    ¬p.Nil ↔ ∃ (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q := by
  cases p <;> simp [*]

@[elab_as_elim]
def notNilRec {motive : {u w : V} → (p : G.Walk u w) → (h : ¬p.Nil) → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) → motive (cons h q) not_nil_cons)
    (p : G.Walk u w) : (hp : ¬p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

/-- The second vertex along a non-nil walk. -/
def sndOfNotNil (p : G.Walk v w) (hp : ¬p.Nil) : V :=
  p.notNilRec (@fun _ u _ _ _ => u) hp

@[simp] lemma adj_sndOfNotNil {p : G.Walk v w} (hp : ¬p.Nil) :
    G.Adj v (p.sndOfNotNil hp) :=
  p.notNilRec (fun h _ => h) hp

/-- The walk obtained by removing the first dart of a non-nil walk. -/
def tail (p : G.Walk u v) (hp : ¬p.Nil) : G.Walk (p.sndOfNotNil hp) v :=
  p.notNilRec (fun _ q => q) hp

/-- The first dart of a walk. -/
@[simps]
def firstDart (p : G.Walk v w) (hp : ¬p.Nil) : G.Dart where
  fst := v
  snd := p.sndOfNotNil hp
  is_adj := p.adj_sndOfNotNil hp

lemma edge_firstDart (p : G.Walk v w) (hp : ¬p.Nil) :
    (p.firstDart hp).edge = s(v, p.sndOfNotNil hp) := rfl

@[simp] lemma cons_tail_eq (p : G.Walk u v) (hp : ¬p.Nil) :
    cons (p.adj_sndOfNotNil hp) (p.tail hp) = p :=
  p.notNilRec (fun _ _ => rfl) hp

@[simp] lemma cons_support_tail (p : G.Walk u v) (hp : ¬p.Nil) :
    u :: (p.tail hp).support = p.support := by
  rw [← support_cons, cons_tail_eq]

@[simp] lemma length_tail_add_one {p : G.Walk u v} (hp : ¬p.Nil) :
    (p.tail hp).length + 1 = p.length := by
  rw [← length_cons, cons_tail_eq]

@[simp] lemma nil_copy {p : G.Walk u v} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).Nil = p.Nil := by
  subst_vars; rfl

/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a walk, give the walk up until (and including) that vertex. -/
def takeUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk v u
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then
      by subst u; exact Walk.nil
    else
      cons r (takeUntil p u <| by cases h; exact (hx rfl).elim; assumption)
#align simple_graph.walk.take_until SimpleGraph.Walk.takeUntil

/-- Given a vertex in the support of a walk, give the walk from (and including) that vertex to
the end. In other words, drop vertices from the front of a walk until (and not including)
that vertex. -/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by cases h; exact (hx rfl).elim; assumption
#align simple_graph.walk.drop_until SimpleGraph.Walk.dropUntil

/-- The `takeUntil` and `dropUntil` functions split a walk into two pieces.
The lemma `SimpleGraph.Walk.count_support_takeUntil_eq_one` specifies where this split occurs. -/
@[simp]
theorem take_spec {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).append (p.dropUntil u h) = p := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    rfl
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> subst_vars <;> simp [*]
#align simple_graph.walk.take_spec SimpleGraph.Walk.take_spec

theorem mem_support_iff_exists_append {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]
#align simple_graph.walk.mem_support_iff_exists_append SimpleGraph.Walk.mem_support_iff_exists_append

@[simp]
theorem count_support_takeUntil_eq_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support.count u = 1 := by
  induction p
  · rw [mem_support_nil_iff] at h
    subst u
    simp!
  · cases h
    · simp!
    · simp! only
      split_ifs with h' <;> rw [eq_comm] at h' <;> subst_vars <;> simp! [*, List.count_cons]
#align simple_graph.walk.count_support_take_until_eq_one SimpleGraph.Walk.count_support_takeUntil_eq_one

theorem count_edges_takeUntil_le_one (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
    (p.takeUntil u h).edges.count s(u, x) ≤ 1 := by
  induction' p with u' u' v' w' ha p' ih
  · rw [mem_support_nil_iff] at h
    subst u
    simp!
  · cases h
    · simp!
    · simp! only
      split_ifs with h'
      · subst h'
        simp
      · rw [edges_cons, List.count_cons]
        split_ifs with h''
        · rw [Sym2.eq_iff] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih
#align simple_graph.walk.count_edges_take_until_le_one SimpleGraph.Walk.count_edges_takeUntil_le_one

@[simp]
theorem takeUntil_copy (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl
#align simple_graph.walk.take_until_copy SimpleGraph.Walk.takeUntil_copy

@[simp]
theorem dropUntil_copy (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
  subst_vars
  rfl
#align simple_graph.walk.drop_until_copy SimpleGraph.Walk.dropUntil_copy

theorem support_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx
#align simple_graph.walk.support_take_until_subset SimpleGraph.Walk.support_takeUntil_subset

theorem support_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx
#align simple_graph.walk.support_drop_until_subset SimpleGraph.Walk.support_dropUntil_subset

theorem darts_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inl hx
#align simple_graph.walk.darts_take_until_subset SimpleGraph.Walk.darts_takeUntil_subset

theorem darts_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inr hx
#align simple_graph.walk.darts_drop_until_subset SimpleGraph.Walk.darts_dropUntil_subset

theorem edges_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_takeUntil_subset h)
#align simple_graph.walk.edges_take_until_subset SimpleGraph.Walk.edges_takeUntil_subset

theorem edges_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_dropUntil_subset h)
#align simple_graph.walk.edges_drop_until_subset SimpleGraph.Walk.edges_dropUntil_subset

theorem length_takeUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.le.intro this
#align simple_graph.walk.length_take_until_le SimpleGraph.Walk.length_takeUntil_le

theorem length_dropUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append, add_comm] at this
  exact Nat.le.intro this
#align simple_graph.walk.length_drop_until_le SimpleGraph.Walk.length_dropUntil_le

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)
#align simple_graph.walk.rotate SimpleGraph.Walk.rotate

@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).support.tail ~r c.support.tail := by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, take_spec]
#align simple_graph.walk.support_rotate SimpleGraph.Walk.support_rotate

theorem rotate_darts {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).darts ~r c.darts := by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, take_spec]
#align simple_graph.walk.rotate_darts SimpleGraph.Walk.rotate_darts

theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).edges ~r c.edges :=
  (rotate_darts c h).map _
#align simple_graph.walk.rotate_edges SimpleGraph.Walk.rotate_edges

end WalkDecomp

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not. -/
theorem exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S := by
  induction' p with _ x y w a p' ih
  · cases vS uS
  · by_cases h : y ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨(x, y), a⟩, List.Mem.head _, uS, h⟩
#align simple_graph.walk.exists_boundary_dart SimpleGraph.Walk.exists_boundary_dart

end Walk

/-! ### Mapping paths -/

namespace Walk

variable {G G' G''}

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') {u v : V} : G.Walk u v → G'.Walk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)
#align simple_graph.walk.map SimpleGraph.Walk.map

variable (f : G →g G') (f' : G' →g G'') {u v u' v' : V} (p : G.Walk u v)

@[simp]
theorem map_nil : (nil : G.Walk u u).map f = nil := rfl
#align simple_graph.walk.map_nil SimpleGraph.Walk.map_nil

@[simp]
theorem map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (p.map f) := rfl
#align simple_graph.walk.map_cons SimpleGraph.Walk.map_cons

@[simp]
theorem map_copy (hu : u = u') (hv : v = v') :
    (p.copy hu hv).map f = (p.map f).copy (hu ▸ rfl) (hv ▸ rfl) := by
  subst_vars
  rfl
#align simple_graph.walk.map_copy SimpleGraph.Walk.map_copy

@[simp]
theorem map_id (p : G.Walk u v) : p.map Hom.id = p := by
  induction p with
  | nil => rfl
  | cons _ p' ih => simp [ih p']
#align simple_graph.walk.map_id SimpleGraph.Walk.map_id

@[simp]
theorem map_map : (p.map f).map f' = p.map (f'.comp f) := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]
#align simple_graph.walk.map_map SimpleGraph.Walk.map_map

/-- Unlike categories, for graphs vertex equality is an important notion, so needing to be able to
work with equality of graph homomorphisms is a necessary evil. -/
theorem map_eq_of_eq {f : G →g G'} (f' : G →g G') (h : f = f') :
    p.map f = (p.map f').copy (h ▸ rfl) (h ▸ rfl) := by
  subst_vars
  rfl
#align simple_graph.walk.map_eq_of_eq SimpleGraph.Walk.map_eq_of_eq

@[simp]
theorem map_eq_nil_iff {p : G.Walk u u} : p.map f = nil ↔ p = nil := by cases p <;> simp
#align simple_graph.walk.map_eq_nil_iff SimpleGraph.Walk.map_eq_nil_iff

@[simp]
theorem length_map : (p.map f).length = p.length := by induction p <;> simp [*]
#align simple_graph.walk.length_map SimpleGraph.Walk.length_map

theorem map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).map f = (p.map f).append (q.map f) := by induction p <;> simp [*]
#align simple_graph.walk.map_append SimpleGraph.Walk.map_append

@[simp]
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by induction p <;> simp [map_append, *]
#align simple_graph.walk.reverse_map SimpleGraph.Walk.reverse_map

@[simp]
theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]
#align simple_graph.walk.support_map SimpleGraph.Walk.support_map

@[simp]
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]
#align simple_graph.walk.darts_map SimpleGraph.Walk.darts_map

@[simp]
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    simp only [Walk.map_cons, edges_cons, List.map_cons, Sym2.map_pair_eq, List.cons.injEq,
      true_and, ih]
#align simple_graph.walk.edges_map SimpleGraph.Walk.edges_map

theorem map_injective_of_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Walk.map f : G.Walk u v → G'.Walk (f u) (f v)) := by
  intro p p' h
  induction p with
  | nil =>
    cases p'
    · rfl
    · simp at h
  | cons _ _ ih =>
    cases p' with
    | nil => simp at h
    | cons _ _ =>
      simp only [map_cons, cons.injEq] at h
      cases hinj h.1
      simp only [cons.injEq, heq_iff_eq, true_and_iff]
      apply ih
      simpa using h.2
#align simple_graph.walk.map_injective_of_injective SimpleGraph.Walk.map_injective_of_injective

/-- The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs. -/
@[reducible]
def mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v) : G'.Walk u v :=
  p.map (Hom.mapSpanningSubgraphs h)
#align simple_graph.walk.map_le SimpleGraph.Walk.mapLe

end Walk

/-! ### Transferring between graphs -/

namespace Walk

variable {G} {H : SimpleGraph V}

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[simp]
protected def transfer {u v : V} (p : G.Walk u v)
    (H : SimpleGraph V) (h : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) : H.Walk u v :=
  match p with
  | nil => nil
  | cons' u v w a p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))
#align simple_graph.walk.transfer SimpleGraph.Walk.transfer

variable {u v : V} (p : G.Walk u v)

theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp [*]
#align simple_graph.walk.transfer_self SimpleGraph.Walk.transfer_self

theorem transfer_eq_map_of_le (hp) (GH : G ≤ H) :
    p.transfer H hp = p.map (SimpleGraph.Hom.mapSpanningSubgraphs GH) := by
  induction p <;> simp [*]
#align simple_graph.walk.transfer_eq_map_of_le SimpleGraph.Walk.transfer_eq_map_of_le

@[simp]
theorem edges_transfer (hp) : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp [*]
#align simple_graph.walk.edges_transfer SimpleGraph.Walk.edges_transfer

@[simp]
theorem support_transfer (hp) : (p.transfer H hp).support = p.support := by
  induction p <;> simp [*]
#align simple_graph.walk.support_transfer SimpleGraph.Walk.support_transfer

@[simp]
theorem length_transfer (hp) : (p.transfer H hp).length = p.length := by
  induction p <;> simp [*]
#align simple_graph.walk.length_transfer SimpleGraph.Walk.length_transfer

-- Porting note: this failed the simpNF linter since it was originally of the form
-- `(p.transfer H hp).transfer K hp' = p.transfer K hp''` with `hp'` a function of `hp` and `hp'`.
-- This was a mistake and it's corrected here.
@[simp]
theorem transfer_transfer (hp) {K : SimpleGraph V} (hp') :
    (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer hp ▸ hp') := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons.injEq, heq_eq_eq, true_and]
    apply ih
#align simple_graph.walk.transfer_transfer SimpleGraph.Walk.transfer_transfer

@[simp]
theorem transfer_append (q : G.Walk v w) (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => hpq _ (by simp [he])).append
        (q.transfer H fun e he => hpq _ (by simp [he])) := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp only [Walk.transfer, cons_append, cons.injEq, heq_eq_eq, true_and, ih]
#align simple_graph.walk.transfer_append SimpleGraph.Walk.transfer_append

@[simp]
theorem reverse_transfer (hp) :
    (p.transfer H hp).reverse =
      p.reverse.transfer H (by simp only [edges_reverse, List.mem_reverse]; exact hp) := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp only [transfer_append, Walk.transfer, reverse_nil, reverse_cons, ih]
#align simple_graph.walk.reverse_transfer SimpleGraph.Walk.reverse_transfer

end Walk


/-! ## Deleting edges -/

namespace Walk

variable {G}

/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
@[reducible]
def toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w) (hp : ∀ e, e ∈ p.edges → ¬e ∈ s) :
    (G.deleteEdges s).Walk v w :=
  p.transfer _ <| by
    simp only [edgeSet_deleteEdges, Set.mem_diff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩
#align simple_graph.walk.to_delete_edges SimpleGraph.Walk.toDeleteEdges

@[simp]
theorem toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) :
    (Walk.nil : G.Walk v v).toDeleteEdges s hp = Walk.nil := rfl
#align simple_graph.walk.to_delete_edges_nil SimpleGraph.Walk.toDeleteEdges_nil

@[simp]
theorem toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp) :
    (Walk.cons h p).toDeleteEdges s hp =
      Walk.cons ((deleteEdges_adj _ _ _ _).mpr ⟨h, hp _ (List.Mem.head _)⟩)
        (p.toDeleteEdges s fun _ he => hp _ <| List.Mem.tail _ he) :=
  rfl
#align simple_graph.walk.to_delete_edges_cons SimpleGraph.Walk.toDeleteEdges_cons

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `SimpleGraph.Walk.toDeleteEdges`. -/
abbrev toDeleteEdge (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) :
    (G.deleteEdges {e}).Walk v w :=
  p.toDeleteEdges {e} (fun e' => by contrapose!; simp (config := { contextual := true }) [hp])
#align simple_graph.walk.to_delete_edge SimpleGraph.Walk.toDeleteEdge

@[simp]
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : G.Walk v w} (hp) :
    Walk.map (Hom.mapSpanningSubgraphs (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_of_le, transfer_transfer, transfer_self]
  · intros e
    rw [edges_transfer]
    apply edges_subset_edgeSet p
#align simple_graph.walk.map_to_delete_edges_eq SimpleGraph.Walk.map_toDeleteEdges_eq

@[simp]
theorem toDeleteEdges_copy (s : Set (Sym2 V))
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s (by subst_vars; exact h)).copy hu hv := by
  subst_vars
  rfl
#align simple_graph.walk.to_delete_edges_copy SimpleGraph.Walk.toDeleteEdges_copy

end Walk

variable {G}

/-! ### Walks as subgraphs -/

namespace Walk

/-- The subgraph consisting of the vertices and edges of the walk. -/
@[simp]
protected def toSubgraph {u v : V} : G.Walk u v → G.Subgraph
  | nil => G.singletonSubgraph u
  | cons h p => G.subgraphOfAdj h ⊔ p.toSubgraph
#align simple_graph.walk.to_subgraph SimpleGraph.Walk.toSubgraph

theorem toSubgraph_cons_nil_eq_subgraphOfAdj (h : G.Adj u v) :
    (cons h nil).toSubgraph = G.subgraphOfAdj h := by simp
#align simple_graph.walk.to_subgraph_cons_nil_eq_subgraph_of_adj SimpleGraph.Walk.toSubgraph_cons_nil_eq_subgraphOfAdj

theorem mem_verts_toSubgraph (p : G.Walk u v) : w ∈ p.toSubgraph.verts ↔ w ∈ p.support := by
  induction' p with _ x y z h p' ih
  · simp
  · have : w = y ∨ w ∈ p'.support ↔ w ∈ p'.support :=
      ⟨by rintro (rfl | h) <;> simp [*], by simp (config := { contextual := true })⟩
    simp [ih, or_assoc, this]
#align simple_graph.walk.mem_verts_to_subgraph SimpleGraph.Walk.mem_verts_toSubgraph

lemma start_mem_verts_toSubgraph (p : G.Walk u v) : u ∈ p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

lemma end_mem_verts_toSubgraph (p : G.Walk u v) : v ∈ p.toSubgraph.verts := by
  simp [mem_verts_toSubgraph]

@[simp]
theorem verts_toSubgraph (p : G.Walk u v) : p.toSubgraph.verts = { w | w ∈ p.support } :=
  Set.ext fun _ => p.mem_verts_toSubgraph
#align simple_graph.walk.verts_to_subgraph SimpleGraph.Walk.verts_toSubgraph

theorem mem_edges_toSubgraph (p : G.Walk u v) {e : Sym2 V} :
    e ∈ p.toSubgraph.edgeSet ↔ e ∈ p.edges := by induction p <;> simp [*]
#align simple_graph.walk.mem_edges_to_subgraph SimpleGraph.Walk.mem_edges_toSubgraph

@[simp]
theorem edgeSet_toSubgraph (p : G.Walk u v) : p.toSubgraph.edgeSet = { e | e ∈ p.edges } :=
  Set.ext fun _ => p.mem_edges_toSubgraph
#align simple_graph.walk.edge_set_to_subgraph SimpleGraph.Walk.edgeSet_toSubgraph

@[simp]
theorem toSubgraph_append (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).toSubgraph = p.toSubgraph ⊔ q.toSubgraph := by induction p <;> simp [*, sup_assoc]
#align simple_graph.walk.to_subgraph_append SimpleGraph.Walk.toSubgraph_append

@[simp]
theorem toSubgraph_reverse (p : G.Walk u v) : p.reverse.toSubgraph = p.toSubgraph := by
  induction p with
  | nil => simp
  | cons _ _ _ =>
    simp only [*, Walk.toSubgraph, reverse_cons, toSubgraph_append, subgraphOfAdj_symm]
    rw [sup_comm]
    congr
    ext <;> simp [-Set.bot_eq_empty]
#align simple_graph.walk.to_subgraph_reverse SimpleGraph.Walk.toSubgraph_reverse

@[simp]
theorem toSubgraph_rotate [DecidableEq V] (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).toSubgraph = c.toSubgraph := by
  rw [rotate, toSubgraph_append, sup_comm, ← toSubgraph_append, take_spec]
#align simple_graph.walk.to_subgraph_rotate SimpleGraph.Walk.toSubgraph_rotate

@[simp]
theorem toSubgraph_map (f : G →g G') (p : G.Walk u v) : (p.map f).toSubgraph = p.toSubgraph.map f :=
  by induction p <;> simp [*, Subgraph.map_sup]
#align simple_graph.walk.to_subgraph_map SimpleGraph.Walk.toSubgraph_map

@[simp]
theorem finite_neighborSet_toSubgraph (p : G.Walk u v) : (p.toSubgraph.neighborSet w).Finite := by
  induction p with
  | nil =>
    rw [Walk.toSubgraph, neighborSet_singletonSubgraph]
    apply Set.toFinite
  | cons ha _ ih =>
    rw [Walk.toSubgraph, Subgraph.neighborSet_sup]
    refine Set.Finite.union ?_ ih
    refine Set.Finite.subset ?_ (neighborSet_subgraphOfAdj_subset ha)
    apply Set.toFinite
#align simple_graph.walk.finite_neighbor_set_to_subgraph SimpleGraph.Walk.finite_neighborSet_toSubgraph

lemma toSubgraph_le_induce_support (p : G.Walk u v) :
    p.toSubgraph ≤ (⊤ : G.Subgraph).induce {v | v ∈ p.support} := by
  convert Subgraph.le_induce_top_verts
  exact p.verts_toSubgraph.symm

end Walk

end SimpleGraph

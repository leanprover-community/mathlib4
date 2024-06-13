/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.List.Rotate

#align_import combinatorics.simple_graph.connectivity from "leanprover-community/mathlib"@"b99e2d58a5e6861833fa8de11e51a81144258db4"

/-!

# Graph connectivity

In a simple graph,

* A *walk* is a finite sequence of adjacent vertices, and can be
  thought of equally well as a sequence of directed edges.

* A *trail* is a walk whose edges each appear no more than once.

* A *path* is a trail whose vertices appear no more than once.

* A *cycle* is a nonempty trail whose first and last vertices are the
  same and whose vertices except for the first appear no more than once.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions
  `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'`)

* `SimpleGraph.Walk.IsTrail`, `SimpleGraph.Walk.IsPath`, and `SimpleGraph.Walk.IsCycle`.

* `SimpleGraph.Path`

* `SimpleGraph.Walk.map` and `SimpleGraph.Path.map` for the induced map on walks,
  given an (injective) graph homomorphism.

* `SimpleGraph.Reachable` for the relation of whether there exists
  a walk between a given pair of vertices

* `SimpleGraph.Preconnected` and `SimpleGraph.Connected` are predicates
  on simple graphs for whether every vertex can be reached from every other,
  and in the latter case, whether the vertex type is nonempty.

* `SimpleGraph.ConnectedComponent` is the type of connected components of
  a given graph.

* `SimpleGraph.IsBridge` for whether an edge is a bridge edge

## Main statements

* `SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem` characterizes bridge edges in terms of
  there being no cycle containing them.

## Tags
walks, trails, paths, circuits, cycles, bridge edges

-/

open Function

universe u v w

namespace SimpleGraph

variable {V : Type u} {V' : Type v} {V'' : Type w}
variable (G : SimpleGraph V) (G' : SimpleGraph V') (G'' : SimpleGraph V'')

/-- A walk is a sequence of adjacent vertices.  For vertices `u v : V`,
the type `walk u v` consists of all walks starting at `u` and ending at `v`.

We say that a walk *visits* the vertices it contains.  The set of vertices a
walk visits is `SimpleGraph.Walk.support`.

See `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'` for patterns that
can be useful in definitions since they make the vertices explicit. -/
inductive Walk : V → V → Type u
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
protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p
#align simple_graph.walk.copy SimpleGraph.Walk.copy

@[simp]
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl
#align simple_graph.walk.copy_rfl_rfl SimpleGraph.Walk.copy_rfl_rfl

@[simp]
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl
#align simple_graph.walk.copy_copy SimpleGraph.Walk.copy_copy

@[simp]
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = Walk.nil := by
  subst_vars
  rfl
#align simple_graph.walk.copy_nil SimpleGraph.Walk.copy_nil

theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl
#align simple_graph.walk.copy_cons SimpleGraph.Walk.copy_cons

@[simp]
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    Walk.cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl
#align simple_graph.walk.cons_copy SimpleGraph.Walk.cons_copy

theorem exists_eq_cons_of_ne {u v : V} (hne : u ≠ v) :
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
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
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
theorem append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
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
    refine ⟨y, cons h q, h'', ?_⟩
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
  | cons _ _ ih => simp [ih, Nat.succ_add, Nat.add_assoc]
#align simple_graph.walk.length_reverse_aux SimpleGraph.Walk.length_reverseAux

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]
#align simple_graph.walk.length_reverse SimpleGraph.Walk.length_reverse

theorem eq_of_length_eq_zero {u v : V} : ∀ {p : G.Walk u v}, p.length = 0 → u = v
  | nil, _ => rfl
#align simple_graph.walk.eq_of_length_eq_zero SimpleGraph.Walk.eq_of_length_eq_zero

theorem adj_of_length_eq_one {u v : V} : ∀ {p : G.Walk u v}, p.length = 1 → G.Adj u v
  | cons h nil, _ => h

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

theorem getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : ℕ) :
    (p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i with
  | nil => simp
  | cons h p ih => cases i <;> simp [getVert, ih, Nat.succ_lt_succ_iff]

theorem getVert_reverse {u v : V} (p : G.Walk u v) (i : ℕ) :
    p.reverse.getVert i = p.getVert (p.length - i) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi =>
      rw [Nat.succ_sub hi.le]
      simp [getVert]
    next hi =>
      obtain rfl | hi' := Nat.eq_or_lt_of_not_lt hi
      · simp [getVert]
      · rw [Nat.eq_add_of_sub_eq (Nat.sub_pos_of_lt hi') rfl, Nat.sub_eq_zero_of_le hi']
        simp [getVert]

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

theorem mem_support_iff {u v w : V} (p : G.Walk u v) :
    w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by cases p <;> simp
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
theorem subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
  simp only [Walk.support_append, List.subset_append_left]
#align simple_graph.walk.subset_support_append_left SimpleGraph.Walk.subset_support_append_left

@[simp]
theorem subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support := by
  intro h
  simp (config := { contextual := true }) only [mem_support_append_iff, or_true_iff, imp_true_iff]
#align simple_graph.walk.subset_support_append_right SimpleGraph.Walk.subset_support_append_right

theorem coe_support {u v : V} (p : G.Walk u v) :
    (p.support : Multiset V) = {u} + p.support.tail := by cases p <;> rfl
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

variable {u v w : V}

@[simp] lemma nil_nil : (nil : G.Walk u u).Nil := Nil.nil

@[simp] lemma not_nil_cons {h : G.Adj u v} {p : G.Walk v w} : ¬ (cons h p).Nil := nofun

instance (p : G.Walk v w) : Decidable p.Nil :=
  match p with
  | nil => isTrue .nil
  | cons _ _ => isFalse nofun

protected lemma Nil.eq {p : G.Walk v w} : p.Nil → v = w | .nil => rfl

lemma not_nil_of_ne {p : G.Walk v w} : v ≠ w → ¬ p.Nil := mt Nil.eq

lemma nil_iff_support_eq {p : G.Walk v w} : p.Nil ↔ p.support = [v] := by
  cases p <;> simp

lemma nil_iff_length_eq {p : G.Walk v w} : p.Nil ↔ p.length = 0 := by
  cases p <;> simp

lemma not_nil_iff {p : G.Walk v w} :
    ¬ p.Nil ↔ ∃ (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q := by
  cases p <;> simp [*]

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
lemma nil_iff_eq_nil : ∀ {p : G.Walk v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

alias ⟨Nil.eq_nil, _⟩ := nil_iff_eq_nil

@[elab_as_elim]
def notNilRec {motive : {u w : V} → (p : G.Walk u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) → motive (cons h q) not_nil_cons)
    (p : G.Walk u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

/-- The second vertex along a non-nil walk. -/
def sndOfNotNil (p : G.Walk v w) (hp : ¬ p.Nil) : V :=
  p.notNilRec (@fun _ u _ _ _ => u) hp

@[simp] lemma adj_sndOfNotNil {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v (p.sndOfNotNil hp) :=
  p.notNilRec (fun h _ => h) hp

/-- The walk obtained by removing the first dart of a non-nil walk. -/
def tail (p : G.Walk u v) (hp : ¬ p.Nil) : G.Walk (p.sndOfNotNil hp) v :=
  p.notNilRec (fun _ q => q) hp

/-- The first dart of a walk. -/
@[simps]
def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := v
  snd := p.sndOfNotNil hp
  adj := p.adj_sndOfNotNil hp

lemma edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.firstDart hp).edge = s(v, p.sndOfNotNil hp) := rfl

variable {x y : V} -- TODO: rename to u, v, w instead?

@[simp] lemma cons_tail_eq (p : G.Walk x y) (hp : ¬ p.Nil) :
    cons (p.adj_sndOfNotNil hp) (p.tail hp) = p :=
  p.notNilRec (fun _ _ => rfl) hp

@[simp] lemma cons_support_tail (p : G.Walk x y) (hp : ¬p.Nil) :
    x :: (p.tail hp).support = p.support := by
  rw [← support_cons, cons_tail_eq]

@[simp] lemma length_tail_add_one {p : G.Walk x y} (hp : ¬ p.Nil) :
    (p.tail hp).length + 1 = p.length := by
  rw [← length_cons, cons_tail_eq]

@[simp] lemma nil_copy {x' y' : V} {p : G.Walk x y} (hx : x = x') (hy : y = y') :
    (p.copy hx hy).Nil = p.Nil := by
  subst_vars; rfl

@[simp] lemma support_tail (p : G.Walk v v) (hp) :
    (p.tail hp).support = p.support.tail := by
  rw [← cons_support_tail p hp, List.tail_cons]

/-! ### Trails, paths, circuits, cycles -/

/-- A *trail* is a walk with no repeating edges. -/
@[mk_iff isTrail_def]
structure IsTrail {u v : V} (p : G.Walk u v) : Prop where
  edges_nodup : p.edges.Nodup
#align simple_graph.walk.is_trail SimpleGraph.Walk.IsTrail
#align simple_graph.walk.is_trail_def SimpleGraph.Walk.isTrail_def

/-- A *path* is a walk with no repeating vertices.
Use `SimpleGraph.Walk.IsPath.mk'` for a simpler constructor. -/
structure IsPath {u v : V} (p : G.Walk u v) extends IsTrail p : Prop where
  support_nodup : p.support.Nodup
#align simple_graph.walk.is_path SimpleGraph.Walk.IsPath

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsPath.isTrail {p : Walk G u v}(h : IsPath p) : IsTrail p := h.toIsTrail
#align simple_graph.walk.is_path.to_trail SimpleGraph.Walk.IsPath.isTrail

/-- A *circuit* at `u : V` is a nonempty trail beginning and ending at `u`. -/
@[mk_iff isCircuit_def]
structure IsCircuit {u : V} (p : G.Walk u u) extends IsTrail p : Prop where
  ne_nil : p ≠ nil
#align simple_graph.walk.is_circuit SimpleGraph.Walk.IsCircuit
#align simple_graph.walk.is_circuit_def SimpleGraph.Walk.isCircuit_def

-- Porting note: used to use `extends to_trail : is_trail p` in structure
protected lemma IsCircuit.isTrail {p : Walk G u u} (h : IsCircuit p) : IsTrail p := h.toIsTrail
#align simple_graph.walk.is_circuit.to_trail SimpleGraph.Walk.IsCircuit.isTrail

/-- A *cycle* at `u : V` is a circuit at `u` whose only repeating vertex
is `u` (which appears exactly twice). -/
structure IsCycle {u : V} (p : G.Walk u u) extends IsCircuit p : Prop where
  support_nodup : p.support.tail.Nodup
#align simple_graph.walk.is_cycle SimpleGraph.Walk.IsCycle

-- Porting note: used to use `extends to_circuit : is_circuit p` in structure
protected lemma IsCycle.isCircuit {p : Walk G u u} (h : IsCycle p) : IsCircuit p := h.toIsCircuit
#align simple_graph.walk.is_cycle.to_circuit SimpleGraph.Walk.IsCycle.isCircuit

@[simp]
theorem isTrail_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsTrail ↔ p.IsTrail := by
  subst_vars
  rfl
#align simple_graph.walk.is_trail_copy SimpleGraph.Walk.isTrail_copy

theorem IsPath.mk' {u v : V} {p : G.Walk u v} (h : p.support.Nodup) : p.IsPath :=
  ⟨⟨edges_nodup_of_support_nodup h⟩, h⟩
#align simple_graph.walk.is_path.mk' SimpleGraph.Walk.IsPath.mk'

theorem isPath_def {u v : V} (p : G.Walk u v) : p.IsPath ↔ p.support.Nodup :=
  ⟨IsPath.support_nodup, IsPath.mk'⟩
#align simple_graph.walk.is_path_def SimpleGraph.Walk.isPath_def

@[simp]
theorem isPath_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).IsPath ↔ p.IsPath := by
  subst_vars
  rfl
#align simple_graph.walk.is_path_copy SimpleGraph.Walk.isPath_copy

@[simp]
theorem isCircuit_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCircuit ↔ p.IsCircuit := by
  subst_vars
  rfl
#align simple_graph.walk.is_circuit_copy SimpleGraph.Walk.isCircuit_copy

lemma IsCircuit.not_nil {p : G.Walk v v} (hp : IsCircuit p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

theorem isCycle_def {u : V} (p : G.Walk u u) :
    p.IsCycle ↔ p.IsTrail ∧ p ≠ nil ∧ p.support.tail.Nodup :=
  Iff.intro (fun h => ⟨h.1.1, h.1.2, h.2⟩) fun h => ⟨⟨h.1, h.2.1⟩, h.2.2⟩
#align simple_graph.walk.is_cycle_def SimpleGraph.Walk.isCycle_def

@[simp]
theorem isCycle_copy {u u'} (p : G.Walk u u) (hu : u = u') :
    (p.copy hu hu).IsCycle ↔ p.IsCycle := by
  subst_vars
  rfl
#align simple_graph.walk.is_cycle_copy SimpleGraph.Walk.isCycle_copy

lemma IsCycle.not_nil {p : G.Walk v v} (hp : IsCycle p) : ¬ p.Nil := (hp.ne_nil ·.eq_nil)

@[simp]
theorem IsTrail.nil {u : V} : (nil : G.Walk u u).IsTrail :=
  ⟨by simp [edges]⟩
#align simple_graph.walk.is_trail.nil SimpleGraph.Walk.IsTrail.nil

theorem IsTrail.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsTrail → p.IsTrail := by simp [isTrail_def]
#align simple_graph.walk.is_trail.of_cons SimpleGraph.Walk.IsTrail.of_cons

@[simp]
theorem cons_isTrail_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsTrail ↔ p.IsTrail ∧ s(u, v) ∉ p.edges := by simp [isTrail_def, and_comm]
#align simple_graph.walk.cons_is_trail_iff SimpleGraph.Walk.cons_isTrail_iff

theorem IsTrail.reverse {u v : V} (p : G.Walk u v) (h : p.IsTrail) : p.reverse.IsTrail := by
  simpa [isTrail_def] using h
#align simple_graph.walk.is_trail.reverse SimpleGraph.Walk.IsTrail.reverse

@[simp]
theorem reverse_isTrail_iff {u v : V} (p : G.Walk u v) : p.reverse.IsTrail ↔ p.IsTrail := by
  constructor <;>
    · intro h
      convert h.reverse _
      try rw [reverse_reverse]
#align simple_graph.walk.reverse_is_trail_iff SimpleGraph.Walk.reverse_isTrail_iff

theorem IsTrail.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : p.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.1⟩
#align simple_graph.walk.is_trail.of_append_left SimpleGraph.Walk.IsTrail.of_append_left

theorem IsTrail.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsTrail) : q.IsTrail := by
  rw [isTrail_def, edges_append, List.nodup_append] at h
  exact ⟨h.2.1⟩
#align simple_graph.walk.is_trail.of_append_right SimpleGraph.Walk.IsTrail.of_append_right

theorem IsTrail.count_edges_le_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    (e : Sym2 V) : p.edges.count e ≤ 1 :=
  List.nodup_iff_count_le_one.mp h.edges_nodup e
#align simple_graph.walk.is_trail.count_edges_le_one SimpleGraph.Walk.IsTrail.count_edges_le_one

theorem IsTrail.count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Walk u v} (h : p.IsTrail)
    {e : Sym2 V} (he : e ∈ p.edges) : p.edges.count e = 1 :=
  List.count_eq_one_of_mem h.edges_nodup he
#align simple_graph.walk.is_trail.count_edges_eq_one SimpleGraph.Walk.IsTrail.count_edges_eq_one

theorem IsPath.nil {u : V} : (nil : G.Walk u u).IsPath := by constructor <;> simp
#align simple_graph.walk.is_path.nil SimpleGraph.Walk.IsPath.nil

theorem IsPath.of_cons {u v w : V} {h : G.Adj u v} {p : G.Walk v w} :
    (cons h p).IsPath → p.IsPath := by simp [isPath_def]
#align simple_graph.walk.is_path.of_cons SimpleGraph.Walk.IsPath.of_cons

@[simp]
theorem cons_isPath_iff {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).IsPath ↔ p.IsPath ∧ u ∉ p.support := by
  constructor <;> simp (config := { contextual := true }) [isPath_def]
#align simple_graph.walk.cons_is_path_iff SimpleGraph.Walk.cons_isPath_iff

protected lemma IsPath.cons {p : Walk G v w} (hp : p.IsPath) (hu : u ∉ p.support) {h : G.Adj u v} :
    (cons h p).IsPath :=
  (cons_isPath_iff _ _).2 ⟨hp, hu⟩

@[simp]
theorem isPath_iff_eq_nil {u : V} (p : G.Walk u u) : p.IsPath ↔ p = nil := by
  cases p <;> simp [IsPath.nil]
#align simple_graph.walk.is_path_iff_eq_nil SimpleGraph.Walk.isPath_iff_eq_nil

theorem IsPath.reverse {u v : V} {p : G.Walk u v} (h : p.IsPath) : p.reverse.IsPath := by
  simpa [isPath_def] using h
#align simple_graph.walk.is_path.reverse SimpleGraph.Walk.IsPath.reverse

@[simp]
theorem isPath_reverse_iff {u v : V} (p : G.Walk u v) : p.reverse.IsPath ↔ p.IsPath := by
  constructor <;> intro h <;> convert h.reverse; simp
#align simple_graph.walk.is_path_reverse_iff SimpleGraph.Walk.isPath_reverse_iff

theorem IsPath.of_append_left {u v w : V} {p : G.Walk u v} {q : G.Walk v w} :
    (p.append q).IsPath → p.IsPath := by
  simp only [isPath_def, support_append]
  exact List.Nodup.of_append_left
#align simple_graph.walk.is_path.of_append_left SimpleGraph.Walk.IsPath.of_append_left

theorem IsPath.of_append_right {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (h : (p.append q).IsPath) : q.IsPath := by
  rw [← isPath_reverse_iff] at h ⊢
  rw [reverse_append] at h
  apply h.of_append_left
#align simple_graph.walk.is_path.of_append_right SimpleGraph.Walk.IsPath.of_append_right

@[simp]
theorem IsCycle.not_of_nil {u : V} : ¬(nil : G.Walk u u).IsCycle := fun h => h.ne_nil rfl
#align simple_graph.walk.is_cycle.not_of_nil SimpleGraph.Walk.IsCycle.not_of_nil

lemma IsCycle.ne_bot : ∀ {p : G.Walk u u}, p.IsCycle → G ≠ ⊥
  | nil, hp => by cases hp.ne_nil rfl
  | cons h _, hp => by rintro rfl; exact h

lemma IsCycle.three_le_length {v : V} {p : G.Walk v v} (hp : p.IsCycle) : 3 ≤ p.length := by
  have ⟨⟨hp, hp'⟩, _⟩ := hp
  match p with
  | .nil => simp at hp'
  | .cons h .nil => simp at h
  | .cons _ (.cons _ .nil) => simp at hp
  | .cons _ (.cons _ (.cons _ _)) => simp_rw [SimpleGraph.Walk.length_cons]; omega

theorem cons_isCycle_iff {u v : V} (p : G.Walk v u) (h : G.Adj u v) :
    (Walk.cons h p).IsCycle ↔ p.IsPath ∧ ¬s(u, v) ∈ p.edges := by
  simp only [Walk.isCycle_def, Walk.isPath_def, Walk.isTrail_def, edges_cons, List.nodup_cons,
    support_cons, List.tail_cons]
  have : p.support.Nodup → p.edges.Nodup := edges_nodup_of_support_nodup
  tauto
#align simple_graph.walk.cons_is_cycle_iff SimpleGraph.Walk.cons_isCycle_iff

lemma IsPath.tail {p : G.Walk u v} (hp : p.IsPath) (hp' : ¬ p.Nil) : (p.tail hp').IsPath := by
  rw [Walk.isPath_def] at hp ⊢
  rw [← cons_support_tail _ hp', List.nodup_cons] at hp
  exact hp.2

/-! ### About paths -/

instance [DecidableEq V] {u v : V} (p : G.Walk u v) : Decidable p.IsPath := by
  rw [isPath_def]
  infer_instance

theorem IsPath.length_lt [Fintype V] {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    p.length < Fintype.card V := by
  rw [Nat.lt_iff_add_one_le, ← length_support]
  exact hp.support_nodup.length_le_card
#align simple_graph.walk.is_path.length_lt SimpleGraph.Walk.IsPath.length_lt


/-! ### Walk decompositions -/

section WalkDecomp

variable [DecidableEq V]

/-- Given a vertex in the support of a path, give the path up until (and including) that vertex. -/
def takeUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk v u
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then
      by subst u; exact Walk.nil
    else
      cons r (takeUntil p u <| by
        cases h
        · exact (hx rfl).elim
        · assumption)
#align simple_graph.walk.take_until SimpleGraph.Walk.takeUntil

/-- Given a vertex in the support of a path, give the path from (and including) that vertex to
the end. In other words, drop vertices from the front of a path until (and not including)
that vertex. -/
def dropUntil {v w : V} : ∀ (p : G.Walk v w) (u : V), u ∈ p.support → G.Walk u w
  | nil, u, h => by rw [mem_support_nil_iff.mp h]
  | cons r p, u, h =>
    if hx : v = u then by
      subst u
      exact cons r p
    else dropUntil p u <| by
      cases h
      · exact (hx rfl).elim
      · assumption
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

theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
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

theorem count_edges_takeUntil_le_one {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) (x : V) :
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
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl
#align simple_graph.walk.take_until_copy SimpleGraph.Walk.takeUntil_copy

@[simp]
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
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

protected theorem IsTrail.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.takeUntil u h).IsTrail :=
  IsTrail.of_append_left (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_trail.take_until SimpleGraph.Walk.IsTrail.takeUntil

protected theorem IsTrail.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsTrail)
    (h : u ∈ p.support) : (p.dropUntil u h).IsTrail :=
  IsTrail.of_append_right (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_trail.drop_until SimpleGraph.Walk.IsTrail.dropUntil

protected theorem IsPath.takeUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.takeUntil u h).IsPath :=
  IsPath.of_append_left (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_path.take_until SimpleGraph.Walk.IsPath.takeUntil

-- Porting note: p was previously accidentally an explicit argument
protected theorem IsPath.dropUntil {u v w : V} {p : G.Walk v w} (hc : p.IsPath)
    (h : u ∈ p.support) : (p.dropUntil u h).IsPath :=
  IsPath.of_append_right (by rwa [← take_spec _ h] at hc)
#align simple_graph.walk.is_path.drop_until SimpleGraph.Walk.IsPath.dropUntil

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

protected theorem IsTrail.rotate {u v : V} {c : G.Walk v v} (hc : c.IsTrail) (h : u ∈ c.support) :
    (c.rotate h).IsTrail := by
  rw [isTrail_def, (c.rotate_edges h).perm.nodup_iff]
  exact hc.edges_nodup
#align simple_graph.walk.is_trail.rotate SimpleGraph.Walk.IsTrail.rotate

protected theorem IsCircuit.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCircuit)
    (h : u ∈ c.support) : (c.rotate h).IsCircuit := by
  refine ⟨hc.isTrail.rotate _, ?_⟩
  cases c
  · exact (hc.ne_nil rfl).elim
  · intro hn
    have hn' := congr_arg length hn
    rw [rotate, length_append, add_comm, ← length_append, take_spec] at hn'
    simp at hn'
#align simple_graph.walk.is_circuit.rotate SimpleGraph.Walk.IsCircuit.rotate

protected theorem IsCycle.rotate {u v : V} {c : G.Walk v v} (hc : c.IsCycle) (h : u ∈ c.support) :
    (c.rotate h).IsCycle := by
  refine ⟨hc.isCircuit.rotate _, ?_⟩
  rw [List.IsRotated.nodup_iff (support_rotate _ _)]
  exact hc.support_nodup
#align simple_graph.walk.is_cycle.rotate SimpleGraph.Walk.IsCycle.rotate

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


/-! ### Type of paths -/

/-- The type for paths between two vertices. -/
abbrev Path (u v : V) := { p : G.Walk u v // p.IsPath }
#align simple_graph.path SimpleGraph.Path

namespace Path

variable {G G'}

@[simp]
protected theorem isPath {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsPath := p.property
#align simple_graph.path.is_path SimpleGraph.Path.isPath

@[simp]
protected theorem isTrail {u v : V} (p : G.Path u v) : (p : G.Walk u v).IsTrail :=
  p.property.isTrail
#align simple_graph.path.is_trail SimpleGraph.Path.isTrail

/-- The length-0 path at a vertex. -/
@[refl, simps]
protected def nil {u : V} : G.Path u u :=
  ⟨Walk.nil, Walk.IsPath.nil⟩
#align simple_graph.path.nil SimpleGraph.Path.nil

/-- The length-1 path between a pair of adjacent vertices. -/
@[simps]
def singleton {u v : V} (h : G.Adj u v) : G.Path u v :=
  ⟨Walk.cons h Walk.nil, by simp [h.ne]⟩
#align simple_graph.path.singleton SimpleGraph.Path.singleton

theorem mk'_mem_edges_singleton {u v : V} (h : G.Adj u v) :
    s(u, v) ∈ (singleton h : G.Walk u v).edges := by simp [singleton]
#align simple_graph.path.mk_mem_edges_singleton SimpleGraph.Path.mk'_mem_edges_singleton

/-- The reverse of a path is another path.  See also `SimpleGraph.Walk.reverse`. -/
@[symm, simps]
def reverse {u v : V} (p : G.Path u v) : G.Path v u :=
  ⟨Walk.reverse p, p.property.reverse⟩
#align simple_graph.path.reverse SimpleGraph.Path.reverse

theorem count_support_eq_one [DecidableEq V] {u v w : V} {p : G.Path u v}
    (hw : w ∈ (p : G.Walk u v).support) : (p : G.Walk u v).support.count w = 1 :=
  List.count_eq_one_of_mem p.property.support_nodup hw
#align simple_graph.path.count_support_eq_one SimpleGraph.Path.count_support_eq_one

theorem count_edges_eq_one [DecidableEq V] {u v : V} {p : G.Path u v} (e : Sym2 V)
    (hw : e ∈ (p : G.Walk u v).edges) : (p : G.Walk u v).edges.count e = 1 :=
  List.count_eq_one_of_mem p.property.isTrail.edges_nodup hw
#align simple_graph.path.count_edges_eq_one SimpleGraph.Path.count_edges_eq_one

@[simp]
theorem nodup_support {u v : V} (p : G.Path u v) : (p : G.Walk u v).support.Nodup :=
  (Walk.isPath_def _).mp p.property
#align simple_graph.path.nodup_support SimpleGraph.Path.nodup_support

theorem loop_eq {v : V} (p : G.Path v v) : p = Path.nil := by
  obtain ⟨_ | _, h⟩ := p
  · rfl
  · simp at h
#align simple_graph.path.loop_eq SimpleGraph.Path.loop_eq

theorem not_mem_edges_of_loop {v : V} {e : Sym2 V} {p : G.Path v v} :
    ¬e ∈ (p : G.Walk v v).edges := by simp [p.loop_eq]
#align simple_graph.path.not_mem_edges_of_loop SimpleGraph.Path.not_mem_edges_of_loop

theorem cons_isCycle {u v : V} (p : G.Path v u) (h : G.Adj u v)
    (he : ¬s(u, v) ∈ (p : G.Walk v u).edges) : (Walk.cons h ↑p).IsCycle := by
  simp [Walk.isCycle_def, Walk.cons_isTrail_iff, he]
#align simple_graph.path.cons_is_cycle SimpleGraph.Path.cons_isCycle

end Path


/-! ### Walks to paths -/

namespace Walk

variable {G} [DecidableEq V]

/-- Given a walk, produces a walk from it by bypassing subwalks between repeated vertices.
The result is a path, as shown in `SimpleGraph.Walk.bypass_isPath`.
This is packaged up in `SimpleGraph.Walk.toPath`. -/
def bypass {u v : V} : G.Walk u v → G.Walk u v
  | nil => nil
  | cons ha p =>
    let p' := p.bypass
    if hs : u ∈ p'.support then
      p'.dropUntil u hs
    else
      cons ha p'
#align simple_graph.walk.bypass SimpleGraph.Walk.bypass

@[simp]
theorem bypass_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).bypass = p.bypass.copy hu hv := by
  subst_vars
  rfl
#align simple_graph.walk.bypass_copy SimpleGraph.Walk.bypass_copy

theorem bypass_isPath {u v : V} (p : G.Walk u v) : p.bypass.IsPath := by
  induction p with
  | nil => simp!
  | cons _ p' ih =>
    simp only [bypass]
    split_ifs with hs
    · exact ih.dropUntil hs
    · simp [*, cons_isPath_iff]
#align simple_graph.walk.bypass_is_path SimpleGraph.Walk.bypass_isPath

theorem length_bypass_le {u v : V} (p : G.Walk u v) : p.bypass.length ≤ p.length := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    simp only [bypass]
    split_ifs
    · trans
      · apply length_dropUntil_le
      rw [length_cons]
      omega
    · rw [length_cons, length_cons]
      exact Nat.add_le_add_right ih 1
#align simple_graph.walk.length_bypass_le SimpleGraph.Walk.length_bypass_le

lemma bypass_eq_self_of_length_le {u v : V} (p : G.Walk u v) (h : p.length ≤ p.bypass.length) :
    p.bypass = p := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [Walk.bypass]
    split_ifs with hb
    · exfalso
      simp only [hb, Walk.bypass, Walk.length_cons, dif_pos] at h
      apply Nat.not_succ_le_self p.length
      calc p.length + 1
        _ ≤ (p.bypass.dropUntil _ _).length := h
        _ ≤ p.bypass.length := Walk.length_dropUntil_le p.bypass hb
        _ ≤ p.length := Walk.length_bypass_le _
    · simp only [hb, Walk.bypass, Walk.length_cons, not_false_iff, dif_neg,
        Nat.add_le_add_iff_right] at h
      rw [ih h]

/-- Given a walk, produces a path with the same endpoints using `SimpleGraph.Walk.bypass`. -/
def toPath {u v : V} (p : G.Walk u v) : G.Path u v :=
  ⟨p.bypass, p.bypass_isPath⟩
#align simple_graph.walk.to_path SimpleGraph.Walk.toPath

theorem support_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.support ⊆ p.support := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (support_dropUntil_subset _ _)
      apply List.subset_cons_of_subset
      assumption
    · rw [support_cons]
      apply List.cons_subset_cons
      assumption
#align simple_graph.walk.support_bypass_subset SimpleGraph.Walk.support_bypass_subset

theorem support_toPath_subset {u v : V} (p : G.Walk u v) :
    (p.toPath : G.Walk u v).support ⊆ p.support :=
  support_bypass_subset _
#align simple_graph.walk.support_to_path_subset SimpleGraph.Walk.support_toPath_subset

theorem darts_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.darts ⊆ p.darts := by
  induction p with
  | nil => simp!
  | cons _ _ ih =>
    simp! only
    split_ifs
    · apply List.Subset.trans (darts_dropUntil_subset _ _)
      apply List.subset_cons_of_subset _ ih
    · rw [darts_cons]
      exact List.cons_subset_cons _ ih
#align simple_graph.walk.darts_bypass_subset SimpleGraph.Walk.darts_bypass_subset

theorem edges_bypass_subset {u v : V} (p : G.Walk u v) : p.bypass.edges ⊆ p.edges :=
  List.map_subset _ p.darts_bypass_subset
#align simple_graph.walk.edges_bypass_subset SimpleGraph.Walk.edges_bypass_subset

theorem darts_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).darts ⊆ p.darts :=
  darts_bypass_subset _
#align simple_graph.walk.darts_to_path_subset SimpleGraph.Walk.darts_toPath_subset

theorem edges_toPath_subset {u v : V} (p : G.Walk u v) : (p.toPath : G.Walk u v).edges ⊆ p.edges :=
  edges_bypass_subset _
#align simple_graph.walk.edges_to_path_subset SimpleGraph.Walk.edges_toPath_subset

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

variable {p f}

theorem map_isPath_of_injective (hinj : Function.Injective f) (hp : p.IsPath) :
    (p.map f).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [Walk.cons_isPath_iff] at hp
    simp only [map_cons, cons_isPath_iff, ih hp.1, support_map, List.mem_map, not_exists, not_and,
      true_and]
    intro x hx hf
    cases hinj hf
    exact hp.2 hx
#align simple_graph.walk.map_is_path_of_injective SimpleGraph.Walk.map_isPath_of_injective

protected theorem IsPath.of_map {f : G →g G'} (hp : (p.map f).IsPath) : p.IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, Walk.cons_isPath_iff, support_map] at hp
    rw [Walk.cons_isPath_iff]
    cases' hp with hp1 hp2
    refine ⟨ih hp1, ?_⟩
    contrapose! hp2
    exact List.mem_map_of_mem f hp2
#align simple_graph.walk.is_path.of_map SimpleGraph.Walk.IsPath.of_map

theorem map_isPath_iff_of_injective (hinj : Function.Injective f) : (p.map f).IsPath ↔ p.IsPath :=
  ⟨IsPath.of_map, map_isPath_of_injective hinj⟩
#align simple_graph.walk.map_is_path_iff_of_injective SimpleGraph.Walk.map_isPath_iff_of_injective

theorem map_isTrail_iff_of_injective (hinj : Function.Injective f) :
    (p.map f).IsTrail ↔ p.IsTrail := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    rw [map_cons, cons_isTrail_iff, ih, cons_isTrail_iff]
    apply and_congr_right'
    rw [← Sym2.map_pair_eq, edges_map, ← List.mem_map_of_injective (Sym2.map.injective hinj)]
#align simple_graph.walk.map_is_trail_iff_of_injective SimpleGraph.Walk.map_isTrail_iff_of_injective

alias ⟨_, map_isTrail_of_injective⟩ := map_isTrail_iff_of_injective
#align simple_graph.walk.map_is_trail_of_injective SimpleGraph.Walk.map_isTrail_of_injective

theorem map_isCycle_iff_of_injective {p : G.Walk u u} (hinj : Function.Injective f) :
    (p.map f).IsCycle ↔ p.IsCycle := by
  rw [isCycle_def, isCycle_def, map_isTrail_iff_of_injective hinj, Ne, map_eq_nil_iff,
    support_map, ← List.map_tail, List.nodup_map_iff hinj]
#align simple_graph.walk.map_is_cycle_iff_of_injective SimpleGraph.Walk.map_isCycle_iff_of_injective

alias ⟨_, IsCycle.map⟩ := map_isCycle_iff_of_injective
#align simple_graph.walk.map_is_cycle_of_injective SimpleGraph.Walk.IsCycle.map

variable (p f)

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
abbrev mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v) : G'.Walk u v :=
  p.map (Hom.mapSpanningSubgraphs h)
#align simple_graph.walk.map_le SimpleGraph.Walk.mapLe

@[simp]
theorem mapLe_isTrail {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsTrail ↔ p.IsTrail :=
  map_isTrail_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_trail SimpleGraph.Walk.mapLe_isTrail

alias ⟨IsTrail.of_mapLe, IsTrail.mapLe⟩ := mapLe_isTrail
#align simple_graph.walk.is_trail.of_map_le SimpleGraph.Walk.IsTrail.of_mapLe
#align simple_graph.walk.is_trail.map_le SimpleGraph.Walk.IsTrail.mapLe

@[simp]
theorem mapLe_isPath {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} {p : G.Walk u v} :
    (p.mapLe h).IsPath ↔ p.IsPath :=
  map_isPath_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_path SimpleGraph.Walk.mapLe_isPath

alias ⟨IsPath.of_mapLe, IsPath.mapLe⟩ := mapLe_isPath
#align simple_graph.walk.is_path.of_map_le SimpleGraph.Walk.IsPath.of_mapLe
#align simple_graph.walk.is_path.map_le SimpleGraph.Walk.IsPath.mapLe

@[simp]
theorem mapLe_isCycle {G G' : SimpleGraph V} (h : G ≤ G') {u : V} {p : G.Walk u u} :
    (p.mapLe h).IsCycle ↔ p.IsCycle :=
  map_isCycle_iff_of_injective Function.injective_id
#align simple_graph.walk.map_le_is_cycle SimpleGraph.Walk.mapLe_isCycle

alias ⟨IsCycle.of_mapLe, IsCycle.mapLe⟩ := mapLe_isCycle
#align simple_graph.walk.is_cycle.of_map_le SimpleGraph.Walk.IsCycle.of_mapLe
#align simple_graph.walk.is_cycle.map_le SimpleGraph.Walk.IsCycle.mapLe

end Walk

namespace Path

variable {G G'}

/-- Given an injective graph homomorphism, map paths to paths. -/
@[simps]
protected def map (f : G →g G') (hinj : Function.Injective f) {u v : V} (p : G.Path u v) :
    G'.Path (f u) (f v) :=
  ⟨Walk.map f p, Walk.map_isPath_of_injective hinj p.2⟩
#align simple_graph.path.map SimpleGraph.Path.map

theorem map_injective {f : G →g G'} (hinj : Function.Injective f) (u v : V) :
    Function.Injective (Path.map f hinj : G.Path u v → G'.Path (f u) (f v)) := by
  rintro ⟨p, hp⟩ ⟨p', hp'⟩ h
  simp only [Path.map, Subtype.coe_mk, Subtype.mk.injEq] at h
  simp [Walk.map_injective_of_injective hinj u v h]
#align simple_graph.path.map_injective SimpleGraph.Path.map_injective

/-- Given a graph embedding, map paths to paths. -/
@[simps!]
protected def mapEmbedding (f : G ↪g G') {u v : V} (p : G.Path u v) : G'.Path (f u) (f v) :=
  Path.map f.toHom f.injective p
#align simple_graph.path.map_embedding SimpleGraph.Path.mapEmbedding

theorem mapEmbedding_injective (f : G ↪g G') (u v : V) :
    Function.Injective (Path.mapEmbedding f : G.Path u v → G'.Path (f u) (f v)) :=
  map_injective f.injective u v
#align simple_graph.path.map_embedding_injective SimpleGraph.Path.mapEmbedding_injective

end Path

/-! ### Transferring between graphs -/

namespace Walk

variable {G}

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[simp]
protected def transfer {u v : V} (p : G.Walk u v)
    (H : SimpleGraph V) (h : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) : H.Walk u v :=
  match p with
  | nil => nil
  | cons' u v w _ p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))
#align simple_graph.walk.transfer SimpleGraph.Walk.transfer

variable {u v : V} (p : G.Walk u v)

theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp [*]
#align simple_graph.walk.transfer_self SimpleGraph.Walk.transfer_self

variable {H : SimpleGraph V}

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

variable {p}

protected theorem IsPath.transfer (hp) (pp : p.IsPath) :
    (p.transfer H hp).IsPath := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons_isPath_iff, support_transfer _ ] at pp ⊢
    exact ⟨ih _ pp.1, pp.2⟩
#align simple_graph.walk.is_path.transfer SimpleGraph.Walk.IsPath.transfer

protected theorem IsCycle.transfer {q : G.Walk u u} (qc : q.IsCycle) (hq) :
    (q.transfer H hq).IsCycle := by
  cases q with
  | nil => simp at qc
  | cons _ q =>
    simp only [edges_cons, List.find?, List.mem_cons, forall_eq_or_imp, mem_edgeSet] at hq
    simp only [Walk.transfer, cons_isCycle_iff, edges_transfer q hq.2] at qc ⊢
    exact ⟨qc.1.transfer hq.2, qc.2⟩
#align simple_graph.walk.is_cycle.transfer SimpleGraph.Walk.IsCycle.transfer

variable (p)

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
theorem transfer_append {w : V} (q : G.Walk v w) (hpq) :
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
abbrev toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w)
    (hp : ∀ e, e ∈ p.edges → ¬e ∈ s) : (G.deleteEdges s).Walk v w :=
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
      Walk.cons (deleteEdges_adj.mpr ⟨h, hp _ (List.Mem.head _)⟩)
        (p.toDeleteEdges s fun _ he => hp _ <| List.Mem.tail _ he) :=
  rfl
#align simple_graph.walk.to_delete_edges_cons SimpleGraph.Walk.toDeleteEdges_cons

variable {v w : V}

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
  intros e
  rw [edges_transfer]
  apply edges_subset_edgeSet p
#align simple_graph.walk.map_to_delete_edges_eq SimpleGraph.Walk.map_toDeleteEdges_eq

protected theorem IsPath.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v w} (h : p.IsPath) (hp) : (p.toDeleteEdges s hp).IsPath :=
  h.transfer _
#align simple_graph.walk.is_path.to_delete_edges SimpleGraph.Walk.IsPath.toDeleteEdges

protected theorem IsCycle.toDeleteEdges (s : Set (Sym2 V))
    {p : G.Walk v v} (h : p.IsCycle) (hp) : (p.toDeleteEdges s hp).IsCycle :=
  h.transfer _
#align simple_graph.walk.is_cycle.to_delete_edges SimpleGraph.Walk.IsCycle.toDeleteEdges

@[simp]
theorem toDeleteEdges_copy {v u u' v' : V} (s : Set (Sym2 V))
    (p : G.Walk u v) (hu : u = u') (hv : v = v') (h) :
    (p.copy hu hv).toDeleteEdges s h =
      (p.toDeleteEdges s (by subst_vars; exact h)).copy hu hv := by
  subst_vars
  rfl
#align simple_graph.walk.to_delete_edges_copy SimpleGraph.Walk.toDeleteEdges_copy

end Walk


/-! ## `Reachable` and `Connected` -/

/-- Two vertices are *reachable* if there is a walk between them.
This is equivalent to `Relation.ReflTransGen` of `G.Adj`.
See `SimpleGraph.reachable_iff_reflTransGen`. -/
def Reachable (u v : V) : Prop := Nonempty (G.Walk u v)
#align simple_graph.reachable SimpleGraph.Reachable

variable {G}

theorem reachable_iff_nonempty_univ {u v : V} :
    G.Reachable u v ↔ (Set.univ : Set (G.Walk u v)).Nonempty :=
  Set.nonempty_iff_univ_nonempty
#align simple_graph.reachable_iff_nonempty_univ SimpleGraph.reachable_iff_nonempty_univ

protected theorem Reachable.elim {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Walk u v → p) : p :=
  Nonempty.elim h hp
#align simple_graph.reachable.elim SimpleGraph.Reachable.elim

protected theorem Reachable.elim_path {p : Prop} {u v : V} (h : G.Reachable u v)
    (hp : G.Path u v → p) : p := by classical exact h.elim fun q => hp q.toPath
#align simple_graph.reachable.elim_path SimpleGraph.Reachable.elim_path

protected theorem Walk.reachable {G : SimpleGraph V} {u v : V} (p : G.Walk u v) : G.Reachable u v :=
  ⟨p⟩
#align simple_graph.walk.reachable SimpleGraph.Walk.reachable

protected theorem Adj.reachable {u v : V} (h : G.Adj u v) : G.Reachable u v :=
  h.toWalk.reachable
#align simple_graph.adj.reachable SimpleGraph.Adj.reachable

@[refl]
protected theorem Reachable.refl (u : V) : G.Reachable u u := ⟨Walk.nil⟩
#align simple_graph.reachable.refl SimpleGraph.Reachable.refl

protected theorem Reachable.rfl {u : V} : G.Reachable u u := Reachable.refl _
#align simple_graph.reachable.rfl SimpleGraph.Reachable.rfl

@[symm]
protected theorem Reachable.symm {u v : V} (huv : G.Reachable u v) : G.Reachable v u :=
  huv.elim fun p => ⟨p.reverse⟩
#align simple_graph.reachable.symm SimpleGraph.Reachable.symm

theorem reachable_comm {u v : V} : G.Reachable u v ↔ G.Reachable v u :=
  ⟨Reachable.symm, Reachable.symm⟩
#align simple_graph.reachable_comm SimpleGraph.reachable_comm

@[trans]
protected theorem Reachable.trans {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    G.Reachable u w :=
  huv.elim fun puv => hvw.elim fun pvw => ⟨puv.append pvw⟩
#align simple_graph.reachable.trans SimpleGraph.Reachable.trans

theorem reachable_iff_reflTransGen (u v : V) :
    G.Reachable u v ↔ Relation.ReflTransGen G.Adj u v := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | nil => rfl
    | cons h' _ ih => exact (Relation.ReflTransGen.single h').trans ih
  · intro h
    induction h with
    | refl => rfl
    | tail _ ha hr => exact Reachable.trans hr ⟨Walk.cons ha Walk.nil⟩
#align simple_graph.reachable_iff_refl_trans_gen SimpleGraph.reachable_iff_reflTransGen

protected theorem Reachable.map {u v : V} {G : SimpleGraph V} {G' : SimpleGraph V'} (f : G →g G')
    (h : G.Reachable u v) : G'.Reachable (f u) (f v) :=
  h.elim fun p => ⟨p.map f⟩
#align simple_graph.reachable.map SimpleGraph.Reachable.map

@[mono]
protected lemma Reachable.mono {u v : V} {G G' : SimpleGraph V}
    (h : G ≤ G') (Guv : G.Reachable u v) : G'.Reachable u v :=
  Guv.map (SimpleGraph.Hom.mapSpanningSubgraphs h)

theorem Iso.reachable_iff {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u v : V} :
    G'.Reachable (φ u) (φ v) ↔ G.Reachable u v :=
  ⟨fun r => φ.left_inv u ▸ φ.left_inv v ▸ r.map φ.symm.toHom, Reachable.map φ.toHom⟩
#align simple_graph.iso.reachable_iff SimpleGraph.Iso.reachable_iff

theorem Iso.symm_apply_reachable {G : SimpleGraph V} {G' : SimpleGraph V'} {φ : G ≃g G'} {u : V}
    {v : V'} : G.Reachable (φ.symm v) u ↔ G'.Reachable v (φ u) := by
  rw [← Iso.reachable_iff, RelIso.apply_symm_apply]
#align simple_graph.iso.symm_apply_reachable SimpleGraph.Iso.symm_apply_reachable

variable (G)

theorem reachable_is_equivalence : Equivalence G.Reachable :=
  Equivalence.mk (@Reachable.refl _ G) (@Reachable.symm _ G) (@Reachable.trans _ G)
#align simple_graph.reachable_is_equivalence SimpleGraph.reachable_is_equivalence

/-- The equivalence relation on vertices given by `SimpleGraph.Reachable`. -/
def reachableSetoid : Setoid V := Setoid.mk _ G.reachable_is_equivalence
#align simple_graph.reachable_setoid SimpleGraph.reachableSetoid

/-- A graph is preconnected if every pair of vertices is reachable from one another. -/
def Preconnected : Prop := ∀ u v : V, G.Reachable u v
#align simple_graph.preconnected SimpleGraph.Preconnected

theorem Preconnected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Preconnected) : H.Preconnected :=
  hf.forall₂.2 fun _ _ => Nonempty.map (Walk.map _) <| hG _ _
#align simple_graph.preconnected.map SimpleGraph.Preconnected.map

@[mono]
protected lemma Preconnected.mono  {G G' : SimpleGraph V} (h : G ≤ G') (hG : G.Preconnected) :
    G'.Preconnected := fun u v => (hG u v).mono h

lemma top_preconnected : (⊤ : SimpleGraph V).Preconnected := fun x y => by
  if h : x = y then rw [h] else exact Adj.reachable h

theorem Iso.preconnected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Preconnected ↔ H.Preconnected :=
  ⟨Preconnected.map e.toHom e.toEquiv.surjective,
    Preconnected.map e.symm.toHom e.symm.toEquiv.surjective⟩
#align simple_graph.iso.preconnected_iff SimpleGraph.Iso.preconnected_iff

/-- A graph is connected if it's preconnected and contains at least one vertex.
This follows the convention observed by mathlib that something is connected iff it has
exactly one connected component.

There is a `CoeFun` instance so that `h u v` can be used instead of `h.Preconnected u v`. -/
@[mk_iff]
structure Connected : Prop where
  protected preconnected : G.Preconnected
  protected [nonempty : Nonempty V]
#align simple_graph.connected SimpleGraph.Connected

lemma connected_iff_exists_forall_reachable : G.Connected ↔ ∃ v, ∀ w, G.Reachable v w := by
  rw [connected_iff]
  constructor
  · rintro ⟨hp, ⟨v⟩⟩
    exact ⟨v, fun w => hp v w⟩
  · rintro ⟨v, h⟩
    exact ⟨fun u w => (h u).symm.trans (h w), ⟨v⟩⟩

instance : CoeFun G.Connected fun _ => ∀ u v : V, G.Reachable u v := ⟨fun h => h.preconnected⟩

theorem Connected.map {G : SimpleGraph V} {H : SimpleGraph V'} (f : G →g H) (hf : Surjective f)
    (hG : G.Connected) : H.Connected :=
  haveI := hG.nonempty.map f
  ⟨hG.preconnected.map f hf⟩
#align simple_graph.connected.map SimpleGraph.Connected.map

@[mono]
protected lemma Connected.mono {G G' : SimpleGraph V} (h : G ≤ G')
    (hG : G.Connected) : G'.Connected where
  preconnected := hG.preconnected.mono h
  nonempty := hG.nonempty

lemma top_connected [Nonempty V] : (⊤ : SimpleGraph V).Connected where
  preconnected := top_preconnected

theorem Iso.connected_iff {G : SimpleGraph V} {H : SimpleGraph V'} (e : G ≃g H) :
    G.Connected ↔ H.Connected :=
  ⟨Connected.map e.toHom e.toEquiv.surjective, Connected.map e.symm.toHom e.symm.toEquiv.surjective⟩
#align simple_graph.iso.connected_iff SimpleGraph.Iso.connected_iff

/-- The quotient of `V` by the `SimpleGraph.Reachable` relation gives the connected
components of a graph. -/
def ConnectedComponent := Quot G.Reachable
#align simple_graph.connected_component SimpleGraph.ConnectedComponent

/-- Gives the connected component containing a particular vertex. -/
def connectedComponentMk (v : V) : G.ConnectedComponent := Quot.mk G.Reachable v
#align simple_graph.connected_component_mk SimpleGraph.connectedComponentMk

variable {G G' G''}

namespace ConnectedComponent

@[simps]
instance inhabited [Inhabited V] : Inhabited G.ConnectedComponent :=
  ⟨G.connectedComponentMk default⟩
#align simple_graph.connected_component.inhabited SimpleGraph.ConnectedComponent.inhabited

@[elab_as_elim]
protected theorem ind {β : G.ConnectedComponent → Prop}
    (h : ∀ v : V, β (G.connectedComponentMk v)) (c : G.ConnectedComponent) : β c :=
  Quot.ind h c
#align simple_graph.connected_component.ind SimpleGraph.ConnectedComponent.ind

@[elab_as_elim]
protected theorem ind₂ {β : G.ConnectedComponent → G.ConnectedComponent → Prop}
    (h : ∀ v w : V, β (G.connectedComponentMk v) (G.connectedComponentMk w))
    (c d : G.ConnectedComponent) : β c d :=
  Quot.induction_on₂ c d h
#align simple_graph.connected_component.ind₂ SimpleGraph.ConnectedComponent.ind₂

protected theorem sound {v w : V} :
    G.Reachable v w → G.connectedComponentMk v = G.connectedComponentMk w :=
  Quot.sound
#align simple_graph.connected_component.sound SimpleGraph.ConnectedComponent.sound

protected theorem exact {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w → G.Reachable v w :=
  @Quotient.exact _ G.reachableSetoid _ _
#align simple_graph.connected_component.exact SimpleGraph.ConnectedComponent.exact

@[simp]
protected theorem eq {v w : V} :
    G.connectedComponentMk v = G.connectedComponentMk w ↔ G.Reachable v w :=
  @Quotient.eq' _ G.reachableSetoid _ _
#align simple_graph.connected_component.eq SimpleGraph.ConnectedComponent.eq

theorem connectedComponentMk_eq_of_adj {v w : V} (a : G.Adj v w) :
    G.connectedComponentMk v = G.connectedComponentMk w :=
  ConnectedComponent.sound a.reachable
#align simple_graph.connected_component.connected_component_mk_eq_of_adj SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj

/-- The `ConnectedComponent` specialization of `Quot.lift`. Provides the stronger
assumption that the vertices are connected by a path. -/
protected def lift {β : Sort*} (f : V → β)
    (h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w) : G.ConnectedComponent → β :=
  Quot.lift f fun v w (h' : G.Reachable v w) => h'.elim_path fun hp => h v w hp hp.2
#align simple_graph.connected_component.lift SimpleGraph.ConnectedComponent.lift

@[simp]
protected theorem lift_mk {β : Sort*} {f : V → β}
    {h : ∀ (v w : V) (p : G.Walk v w), p.IsPath → f v = f w} {v : V} :
    ConnectedComponent.lift f h (G.connectedComponentMk v) = f v :=
  rfl
#align simple_graph.connected_component.lift_mk SimpleGraph.ConnectedComponent.lift_mk

protected theorem «exists» {p : G.ConnectedComponent → Prop} :
    (∃ c : G.ConnectedComponent, p c) ↔ ∃ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).exists
#align simple_graph.connected_component.exists SimpleGraph.ConnectedComponent.exists

protected theorem «forall» {p : G.ConnectedComponent → Prop} :
    (∀ c : G.ConnectedComponent, p c) ↔ ∀ v, p (G.connectedComponentMk v) :=
  (surjective_quot_mk G.Reachable).forall
#align simple_graph.connected_component.forall SimpleGraph.ConnectedComponent.forall

theorem _root_.SimpleGraph.Preconnected.subsingleton_connectedComponent (h : G.Preconnected) :
    Subsingleton G.ConnectedComponent :=
  ⟨ConnectedComponent.ind₂ fun v w => ConnectedComponent.sound (h v w)⟩
#align simple_graph.preconnected.subsingleton_connected_component SimpleGraph.Preconnected.subsingleton_connectedComponent

/-- The map on connected components induced by a graph homomorphism. -/
def map (φ : G →g G') (C : G.ConnectedComponent) : G'.ConnectedComponent :=
  C.lift (fun v => G'.connectedComponentMk (φ v)) fun _ _ p _ =>
    ConnectedComponent.eq.mpr (p.map φ).reachable
#align simple_graph.connected_component.map SimpleGraph.ConnectedComponent.map

@[simp]
theorem map_mk (φ : G →g G') (v : V) :
    (G.connectedComponentMk v).map φ = G'.connectedComponentMk (φ v) :=
  rfl
#align simple_graph.connected_component.map_mk SimpleGraph.ConnectedComponent.map_mk

@[simp]
theorem map_id (C : ConnectedComponent G) : C.map Hom.id = C := by
  refine C.ind ?_
  exact fun _ => rfl
#align simple_graph.connected_component.map_id SimpleGraph.ConnectedComponent.map_id

@[simp]
theorem map_comp (C : G.ConnectedComponent) (φ : G →g G') (ψ : G' →g G'') :
    (C.map φ).map ψ = C.map (ψ.comp φ) := by
  refine C.ind ?_
  exact fun _ => rfl
#align simple_graph.connected_component.map_comp SimpleGraph.ConnectedComponent.map_comp

variable {φ : G ≃g G'} {v : V} {v' : V'}

@[simp]
theorem iso_image_comp_eq_map_iff_eq_comp {C : G.ConnectedComponent} :
    G'.connectedComponentMk (φ v) = C.map ↑(↑φ : G ↪g G') ↔ G.connectedComponentMk v = C := by
  refine C.ind fun u => ?_
  simp only [Iso.reachable_iff, ConnectedComponent.map_mk, RelEmbedding.coe_toRelHom,
    RelIso.coe_toRelEmbedding, ConnectedComponent.eq]
#align simple_graph.connected_component.iso_image_comp_eq_map_iff_eq_comp SimpleGraph.ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp

@[simp]
theorem iso_inv_image_comp_eq_iff_eq_map {C : G.ConnectedComponent} :
    G.connectedComponentMk (φ.symm v') = C ↔ G'.connectedComponentMk v' = C.map φ := by
  refine C.ind fun u => ?_
  simp only [Iso.symm_apply_reachable, ConnectedComponent.eq, ConnectedComponent.map_mk,
    RelEmbedding.coe_toRelHom, RelIso.coe_toRelEmbedding]
#align simple_graph.connected_component.iso_inv_image_comp_eq_iff_eq_map SimpleGraph.ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map

end ConnectedComponent

namespace Iso

/-- An isomorphism of graphs induces a bijection of connected components. -/
@[simps]
def connectedComponentEquiv (φ : G ≃g G') : G.ConnectedComponent ≃ G'.ConnectedComponent where
  toFun := ConnectedComponent.map φ
  invFun := ConnectedComponent.map φ.symm
  left_inv C := ConnectedComponent.ind
    (fun v => congr_arg G.connectedComponentMk (Equiv.left_inv φ.toEquiv v)) C
  right_inv C := ConnectedComponent.ind
    (fun v => congr_arg G'.connectedComponentMk (Equiv.right_inv φ.toEquiv v)) C
#align simple_graph.iso.connected_component_equiv SimpleGraph.Iso.connectedComponentEquiv

@[simp]
theorem connectedComponentEquiv_refl :
    (Iso.refl : G ≃g G).connectedComponentEquiv = Equiv.refl _ := by
  ext ⟨v⟩
  rfl
#align simple_graph.iso.connected_component_equiv_refl SimpleGraph.Iso.connectedComponentEquiv_refl

@[simp]
theorem connectedComponentEquiv_symm (φ : G ≃g G') :
    φ.symm.connectedComponentEquiv = φ.connectedComponentEquiv.symm := by
  ext ⟨_⟩
  rfl
#align simple_graph.iso.connected_component_equiv_symm SimpleGraph.Iso.connectedComponentEquiv_symm

@[simp]
theorem connectedComponentEquiv_trans (φ : G ≃g G') (φ' : G' ≃g G'') :
    connectedComponentEquiv (φ.trans φ') =
    φ.connectedComponentEquiv.trans φ'.connectedComponentEquiv := by
  ext ⟨_⟩
  rfl
#align simple_graph.iso.connected_component_equiv_trans SimpleGraph.Iso.connectedComponentEquiv_trans

end Iso

namespace ConnectedComponent

/-- The set of vertices in a connected component of a graph. -/
def supp (C : G.ConnectedComponent) :=
  { v | G.connectedComponentMk v = C }
#align simple_graph.connected_component.supp SimpleGraph.ConnectedComponent.supp

@[ext]
theorem supp_injective :
    Function.Injective (ConnectedComponent.supp : G.ConnectedComponent → Set V) := by
  refine ConnectedComponent.ind₂ ?_
  intro v w
  simp only [ConnectedComponent.supp, Set.ext_iff, ConnectedComponent.eq, Set.mem_setOf_eq]
  intro h
  rw [reachable_comm, h]
#align simple_graph.connected_component.supp_injective SimpleGraph.ConnectedComponent.supp_injective

@[simp]
theorem supp_inj {C D : G.ConnectedComponent} : C.supp = D.supp ↔ C = D :=
  ConnectedComponent.supp_injective.eq_iff
#align simple_graph.connected_component.supp_inj SimpleGraph.ConnectedComponent.supp_inj

instance : SetLike G.ConnectedComponent V where
  coe := ConnectedComponent.supp
  coe_injective' := ConnectedComponent.supp_injective

@[simp]
theorem mem_supp_iff (C : G.ConnectedComponent) (v : V) :
    v ∈ C.supp ↔ G.connectedComponentMk v = C :=
  Iff.rfl
#align simple_graph.connected_component.mem_supp_iff SimpleGraph.ConnectedComponent.mem_supp_iff

theorem connectedComponentMk_mem {v : V} : v ∈ G.connectedComponentMk v :=
  rfl
#align simple_graph.connected_component.connected_component_mk_mem SimpleGraph.ConnectedComponent.connectedComponentMk_mem

/-- The equivalence between connected components, induced by an isomorphism of graphs,
itself defines an equivalence on the supports of each connected component.
-/
def isoEquivSupp (φ : G ≃g G') (C : G.ConnectedComponent) :
    C.supp ≃ (φ.connectedComponentEquiv C).supp where
  toFun v := ⟨φ v, ConnectedComponent.iso_image_comp_eq_map_iff_eq_comp.mpr v.prop⟩
  invFun v' := ⟨φ.symm v', ConnectedComponent.iso_inv_image_comp_eq_iff_eq_map.mpr v'.prop⟩
  left_inv v := Subtype.ext_val (φ.toEquiv.left_inv ↑v)
  right_inv v := Subtype.ext_val (φ.toEquiv.right_inv ↑v)
#align simple_graph.connected_component.iso_equiv_supp SimpleGraph.ConnectedComponent.isoEquivSupp

end ConnectedComponent

theorem Preconnected.set_univ_walk_nonempty (hconn : G.Preconnected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty := by
  rw [← Set.nonempty_iff_univ_nonempty]
  exact hconn u v
#align simple_graph.preconnected.set_univ_walk_nonempty SimpleGraph.Preconnected.set_univ_walk_nonempty

theorem Connected.set_univ_walk_nonempty (hconn : G.Connected) (u v : V) :
    (Set.univ : Set (G.Walk u v)).Nonempty :=
  hconn.preconnected.set_univ_walk_nonempty u v
#align simple_graph.connected.set_univ_walk_nonempty SimpleGraph.Connected.set_univ_walk_nonempty


/-! ### Walks as subgraphs -/

namespace Walk

variable {u v w : V}

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
theorem toSubgraph_map (f : G →g G') (p : G.Walk u v) :
    (p.map f).toSubgraph = p.toSubgraph.map f := by induction p <;> simp [*, Subgraph.map_sup]
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


/-! ### Walks of a given length -/

section WalkCounting

theorem set_walk_self_length_zero_eq (u : V) : {p : G.Walk u u | p.length = 0} = {Walk.nil} := by
  ext p
  simp
#align simple_graph.set_walk_self_length_zero_eq SimpleGraph.set_walk_self_length_zero_eq

theorem set_walk_length_zero_eq_of_ne {u v : V} (h : u ≠ v) :
    {p : G.Walk u v | p.length = 0} = ∅ := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false_iff]
  exact fun h' => absurd (Walk.eq_of_length_eq_zero h') h
#align simple_graph.set_walk_length_zero_eq_of_ne SimpleGraph.set_walk_length_zero_eq_of_ne

theorem set_walk_length_succ_eq (u v : V) (n : ℕ) :
    {p : G.Walk u v | p.length = n.succ} =
      ⋃ (w : V) (h : G.Adj u w), Walk.cons h '' {p' : G.Walk w v | p'.length = n} := by
  ext p
  cases' p with _ _ w _ huw pwv
  · simp [eq_comm]
  · simp only [Nat.succ_eq_add_one, Set.mem_setOf_eq, Walk.length_cons, add_left_inj,
      Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro rfl
      exact ⟨w, huw, pwv, rfl, rfl⟩
    · rintro ⟨w, huw, pwv, rfl, rfl, rfl⟩
      rfl
#align simple_graph.set_walk_length_succ_eq SimpleGraph.set_walk_length_succ_eq

variable (G) [DecidableEq V]

/-- Walks of length two from `u` to `v` correspond bijectively to common neighbours of `u` and `v`.
Note that `u` and `v` may be the same. -/
@[simps]
def walkLengthTwoEquivCommonNeighbors (u v : V) :
    {p : G.Walk u v // p.length = 2} ≃ G.commonNeighbors u v where
  toFun p := ⟨p.val.getVert 1, match p with
    | ⟨.cons _ (.cons _ .nil), hp⟩ => ⟨‹G.Adj u _›, ‹G.Adj _ v›.symm⟩⟩
  invFun w := ⟨w.prop.1.toWalk.concat w.prop.2.symm, rfl⟩
  left_inv | ⟨.cons _ (.cons _ .nil), hp⟩ => by rfl
  right_inv _ := rfl

section LocallyFinite

variable [LocallyFinite G]

/-- The `Finset` of length-`n` walks from `u` to `v`.
This is used to give `{p : G.walk u v | p.length = n}` a `Fintype` instance, and it
can also be useful as a recursive description of this set when `V` is finite.

See `SimpleGraph.coe_finsetWalkLength_eq` for the relationship between this `Finset` and
the set of length-`n` walks. -/
def finsetWalkLength (n : ℕ) (u v : V) : Finset (G.Walk u v) :=
  match n with
  | 0 =>
    if h : u = v then by
      subst u
      exact {Walk.nil}
    else ∅
  | n + 1 =>
    Finset.univ.biUnion fun (w : G.neighborSet u) =>
      (finsetWalkLength n w v).map ⟨fun p => Walk.cons w.property p, fun _ _ => by simp⟩
#align simple_graph.finset_walk_length SimpleGraph.finsetWalkLength

theorem coe_finsetWalkLength_eq (n : ℕ) (u v : V) :
    (G.finsetWalkLength n u v : Set (G.Walk u v)) = {p : G.Walk u v | p.length = n} := by
  induction' n with n ih generalizing u v
  · obtain rfl | huv := eq_or_ne u v <;> simp [finsetWalkLength, set_walk_length_zero_eq_of_ne, *]
  · simp only [finsetWalkLength, set_walk_length_succ_eq, Finset.coe_biUnion, Finset.mem_coe,
      Finset.mem_univ, Set.iUnion_true]
    ext p
    simp only [mem_neighborSet, Finset.coe_map, Embedding.coeFn_mk, Set.iUnion_coe_set,
      Set.mem_iUnion, Set.mem_image, Finset.mem_coe, Set.mem_setOf_eq]
    congr!
    rename_i w _ q
    have := Set.ext_iff.mp (ih w v) q
    simp only [Finset.mem_coe, Set.mem_setOf_eq] at this
    rw [← this]
#align simple_graph.coe_finset_walk_length_eq SimpleGraph.coe_finsetWalkLength_eq

variable {G}

theorem Walk.mem_finsetWalkLength_iff_length_eq {n : ℕ} {u v : V} (p : G.Walk u v) :
    p ∈ G.finsetWalkLength n u v ↔ p.length = n :=
  Set.ext_iff.mp (G.coe_finsetWalkLength_eq n u v) p
#align simple_graph.walk.mem_finset_walk_length_iff_length_eq SimpleGraph.Walk.mem_finsetWalkLength_iff_length_eq

variable (G)

instance fintypeSetWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v | p.length = n} :=
  Fintype.ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
#align simple_graph.fintype_set_walk_length SimpleGraph.fintypeSetWalkLength

instance fintypeSubtypeWalkLength (u v : V) (n : ℕ) : Fintype {p : G.Walk u v // p.length = n} :=
  fintypeSetWalkLength G u v n

theorem set_walk_length_toFinset_eq (n : ℕ) (u v : V) :
    {p : G.Walk u v | p.length = n}.toFinset = G.finsetWalkLength n u v := by
  ext p
  simp [← coe_finsetWalkLength_eq]
#align simple_graph.set_walk_length_to_finset_eq SimpleGraph.set_walk_length_toFinset_eq

/- See `SimpleGraph.adjMatrix_pow_apply_eq_card_walk` for the cardinality in terms of the `n`th
power of the adjacency matrix. -/
theorem card_set_walk_length_eq (u v : V) (n : ℕ) :
    Fintype.card {p : G.Walk u v | p.length = n} = (G.finsetWalkLength n u v).card :=
  Fintype.card_ofFinset (G.finsetWalkLength n u v) fun p => by
    rw [← Finset.mem_coe, coe_finsetWalkLength_eq]
#align simple_graph.card_set_walk_length_eq SimpleGraph.card_set_walk_length_eq

instance fintypeSetPathLength (u v : V) (n : ℕ) :
    Fintype {p : G.Walk u v | p.IsPath ∧ p.length = n} :=
  Fintype.ofFinset ((G.finsetWalkLength n u v).filter Walk.IsPath) <| by
    simp [Walk.mem_finsetWalkLength_iff_length_eq, and_comm]
#align simple_graph.fintype_set_path_length SimpleGraph.fintypeSetPathLength

end LocallyFinite

section Finite

variable [Fintype V] [DecidableRel G.Adj]

theorem reachable_iff_exists_finsetWalkLength_nonempty (u v : V) :
    G.Reachable u v ↔ ∃ n : Fin (Fintype.card V), (G.finsetWalkLength n u v).Nonempty := by
  constructor
  · intro r
    refine r.elim_path fun p => ?_
    refine ⟨⟨_, p.isPath.length_lt⟩, p, ?_⟩
    simp [Walk.mem_finsetWalkLength_iff_length_eq]
  · rintro ⟨_, p, _⟩
    exact ⟨p⟩
#align simple_graph.reachable_iff_exists_finset_walk_length_nonempty SimpleGraph.reachable_iff_exists_finsetWalkLength_nonempty

instance : DecidableRel G.Reachable := fun u v =>
  decidable_of_iff' _ (reachable_iff_exists_finsetWalkLength_nonempty G u v)

instance : Fintype G.ConnectedComponent :=
  @Quotient.fintype _ _ G.reachableSetoid (inferInstance : DecidableRel G.Reachable)

instance : Decidable G.Preconnected :=
  inferInstanceAs <| Decidable (∀ u v, G.Reachable u v)

instance : Decidable G.Connected := by
  rw [connected_iff, ← Finset.univ_nonempty_iff]
  infer_instance

end Finite

end WalkCounting

section BridgeEdges


/-! ### Bridge edges -/

/-- An edge of a graph is a *bridge* if, after removing it, its incident vertices
are no longer reachable from one another. -/
def IsBridge (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  e ∈ G.edgeSet ∧
    Sym2.lift ⟨fun v w => ¬(G \ fromEdgeSet {e}).Reachable v w, by simp [reachable_comm]⟩ e
#align simple_graph.is_bridge SimpleGraph.IsBridge

theorem isBridge_iff {u v : V} :
    G.IsBridge s(u, v) ↔ G.Adj u v ∧ ¬(G \ fromEdgeSet {s(u, v)}).Reachable u v := Iff.rfl
#align simple_graph.is_bridge_iff SimpleGraph.isBridge_iff

theorem reachable_delete_edges_iff_exists_walk {v w : V} :
    (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔ ∃ p : G.Walk v w, ¬s(v, w) ∈ p.edges := by
  constructor
  · rintro ⟨p⟩
    use p.map (Hom.mapSpanningSubgraphs (by simp))
    simp_rw [Walk.edges_map, List.mem_map, Hom.mapSpanningSubgraphs_apply, Sym2.map_id', id]
    rintro ⟨e, h, rfl⟩
    simpa using p.edges_subset_edgeSet h
  · rintro ⟨p, h⟩
    refine ⟨p.transfer _ fun e ep => ?_⟩
    simp only [edgeSet_sdiff, edgeSet_fromEdgeSet, edgeSet_sdiff_sdiff_isDiag, Set.mem_diff,
      Set.mem_singleton_iff]
    exact ⟨p.edges_subset_edgeSet ep, fun h' => h (h' ▸ ep)⟩
#align simple_graph.reachable_delete_edges_iff_exists_walk SimpleGraph.reachable_delete_edges_iff_exists_walk

theorem isBridge_iff_adj_and_forall_walk_mem_edges {v w : V} :
    G.IsBridge s(v, w) ↔ G.Adj v w ∧ ∀ p : G.Walk v w, s(v, w) ∈ p.edges := by
  rw [isBridge_iff, and_congr_right']
  rw [reachable_delete_edges_iff_exists_walk, not_exists_not]
#align simple_graph.is_bridge_iff_adj_and_forall_walk_mem_edges SimpleGraph.isBridge_iff_adj_and_forall_walk_mem_edges

theorem reachable_deleteEdges_iff_exists_cycle.aux [DecidableEq V] {u v w : V}
    (hb : ∀ p : G.Walk v w, s(v, w) ∈ p.edges) (c : G.Walk u u) (hc : c.IsTrail)
    (he : s(v, w) ∈ c.edges)
    (hw : w ∈ (c.takeUntil v (c.fst_mem_support_of_mem_edges he)).support) : False := by
  have hv := c.fst_mem_support_of_mem_edges he
  -- decompose c into
  --      puw     pwv     pvu
  --   u ----> w ----> v ----> u
  let puw := (c.takeUntil v hv).takeUntil w hw
  let pwv := (c.takeUntil v hv).dropUntil w hw
  let pvu := c.dropUntil v hv
  have : c = (puw.append pwv).append pvu := by simp [puw, pwv, pvu]
  -- We have two walks from v to w
  --      pvu     puw
  --   v ----> u ----> w
  --   |               ^
  --    `-------------'
  --      pwv.reverse
  -- so they both contain the edge s(v, w), but that's a contradiction since c is a trail.
  have hbq := hb (pvu.append puw)
  have hpq' := hb pwv.reverse
  rw [Walk.edges_reverse, List.mem_reverse] at hpq'
  rw [Walk.isTrail_def, this, Walk.edges_append, Walk.edges_append, List.nodup_append_comm,
    ← List.append_assoc, ← Walk.edges_append] at hc
  exact List.disjoint_of_nodup_append hc hbq hpq'
#align simple_graph.reachable_delete_edges_iff_exists_cycle.aux SimpleGraph.reachable_deleteEdges_iff_exists_cycle.aux

-- Porting note: the unused variable checker helped eliminate a good amount of this proof (!)
theorem adj_and_reachable_delete_edges_iff_exists_cycle {v w : V} :
    G.Adj v w ∧ (G \ fromEdgeSet {s(v, w)}).Reachable v w ↔
      ∃ (u : V) (p : G.Walk u u), p.IsCycle ∧ s(v, w) ∈ p.edges := by
  classical
  rw [reachable_delete_edges_iff_exists_walk]
  constructor
  · rintro ⟨h, p, hp⟩
    refine ⟨w, Walk.cons h.symm p.toPath, ?_, ?_⟩
    · apply Path.cons_isCycle
      rw [Sym2.eq_swap]
      intro h
      cases hp (Walk.edges_toPath_subset p h)
    · simp only [Sym2.eq_swap, Walk.edges_cons, List.mem_cons, eq_self_iff_true, true_or_iff]
  · rintro ⟨u, c, hc, he⟩
    refine ⟨c.adj_of_mem_edges he, ?_⟩
    by_contra! hb
    have hb' : ∀ p : G.Walk w v, s(w, v) ∈ p.edges := by
      intro p
      simpa [Sym2.eq_swap] using hb p.reverse
    have hvc : v ∈ c.support := Walk.fst_mem_support_of_mem_edges c he
    refine reachable_deleteEdges_iff_exists_cycle.aux hb' (c.rotate hvc) (hc.isTrail.rotate hvc)
      ?_ (Walk.start_mem_support _)
    rwa [(Walk.rotate_edges c hvc).mem_iff, Sym2.eq_swap]
#align simple_graph.adj_and_reachable_delete_edges_iff_exists_cycle SimpleGraph.adj_and_reachable_delete_edges_iff_exists_cycle

theorem isBridge_iff_adj_and_forall_cycle_not_mem {v w : V} : G.IsBridge s(v, w) ↔
    G.Adj v w ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → s(v, w) ∉ p.edges := by
  rw [isBridge_iff, and_congr_right_iff]
  intro h
  rw [← not_iff_not]
  push_neg
  rw [← adj_and_reachable_delete_edges_iff_exists_cycle]
  simp only [h, true_and_iff]
#align simple_graph.is_bridge_iff_adj_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_adj_and_forall_cycle_not_mem

theorem isBridge_iff_mem_and_forall_cycle_not_mem {e : Sym2 V} :
    G.IsBridge e ↔ e ∈ G.edgeSet ∧ ∀ ⦃u : V⦄ (p : G.Walk u u), p.IsCycle → e ∉ p.edges :=
  Sym2.ind (fun _ _ => isBridge_iff_adj_and_forall_cycle_not_mem) e
#align simple_graph.is_bridge_iff_mem_and_forall_cycle_not_mem SimpleGraph.isBridge_iff_mem_and_forall_cycle_not_mem

end BridgeEdges

end SimpleGraph

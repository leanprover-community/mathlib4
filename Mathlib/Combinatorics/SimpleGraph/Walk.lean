/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!

# Walk

In a simple graph, a *walk* is a finite sequence of adjacent vertices, and can be
thought of equally well as a sequence of directed edges.

**Warning:** graph theorists mean something different by "path" than
do homotopy theorists.  A "walk" in graph theory is a "path" in
homotopy theory.  Another warning: some graph theorists use "path" and
"simple path" for "walk" and "path."

Some definitions and theorems have inspiration from multigraph
counterparts in [Chou1994].

## Main definitions

* `SimpleGraph.Walk` (with accompanying pattern definitions
  `SimpleGraph.Walk.nil'` and `SimpleGraph.Walk.cons'`)

* `SimpleGraph.Walk.map` for the induced map on walks,
  given an (injective) graph homomorphism.

## Tags
walks

-/

-- TODO: split
set_option linter.style.longFile 1700

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

attribute [refl] Walk.nil

@[simps]
instance Walk.instInhabited (v : V) : Inhabited (G.Walk v v) := ⟨Walk.nil⟩

/-- The one-edge walk associated to a pair of adjacent vertices. -/
@[match_pattern, reducible]
def Adj.toWalk {G : SimpleGraph V} {u v : V} (h : G.Adj u v) : G.Walk u v :=
  Walk.cons h Walk.nil

namespace Walk

variable {G}

/-- Pattern to get `Walk.nil` with the vertex as an explicit argument. -/
@[match_pattern]
abbrev nil' (u : V) : G.Walk u u := Walk.nil

/-- Pattern to get `Walk.cons` with the vertices as explicit arguments. -/
@[match_pattern]
abbrev cons' (u v w : V) (h : G.Adj u v) (p : G.Walk v w) : G.Walk u w := Walk.cons h p

/-- Change the endpoints of a walk using equalities. This is helpful for relaxing
definitional equality constraints and to be able to state otherwise difficult-to-state
lemmas. While this is a simple wrapper around `Eq.rec`, it gives a canonical way to write it.

The simp-normal form is for the `copy` to be pushed outward. That way calculations can
occur within the "copy context." -/
protected def copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') : G.Walk u' v' :=
  hu ▸ hv ▸ p

@[simp]
theorem copy_rfl_rfl {u v} (p : G.Walk u v) : p.copy rfl rfl = p := rfl

@[simp]
theorem copy_copy {u v u' v' u'' v''} (p : G.Walk u v)
    (hu : u = u') (hv : v = v') (hu' : u' = u'') (hv' : v' = v'') :
    (p.copy hu hv).copy hu' hv' = p.copy (hu.trans hu') (hv.trans hv') := by
  subst_vars
  rfl

@[simp]
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = Walk.nil := by
  subst_vars
  rfl

theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl

@[simp]
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    Walk.cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl

theorem exists_eq_cons_of_ne {u v : V} (hne : u ≠ v) :
    ∀ (p : G.Walk u v), ∃ (w : V) (h : G.Adj u w) (p' : G.Walk w v), p = cons h p'
  | nil => (hne rfl).elim
  | cons h p' => ⟨_, h, p', rfl⟩

/-- The length of a walk is the number of edges/darts along it. -/
def length {u v : V} : G.Walk u v → ℕ
  | nil => 0
  | cons _ q => q.length.succ

/-- The concatenation of two compatible walks. -/
@[trans]
def append {u v w : V} : G.Walk u v → G.Walk v w → G.Walk u w
  | nil, q => q
  | cons h p, q => cons h (p.append q)

/-- The reversed version of `SimpleGraph.Walk.cons`, concatenating an edge to
the end of a walk. -/
def concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) : G.Walk u w := p.append (cons h nil)

theorem concat_eq_append {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    p.concat h = p.append (cons h nil) := rfl

/-- The concatenation of the reverse of the first walk with the second walk. -/
protected def reverseAux {u v w : V} : G.Walk u v → G.Walk u w → G.Walk v w
  | nil, q => q
  | cons h p, q => Walk.reverseAux p (cons (G.symm h) q)

/-- The walk in reverse. -/
@[symm]
def reverse {u v : V} (w : G.Walk u v) : G.Walk v u := w.reverseAux nil

/-- Get the `n`th vertex from a walk, where `n` is generally expected to be
between `0` and `p.length`, inclusive.
If `n` is greater than or equal to `p.length`, the result is the path's endpoint. -/
def getVert {u v : V} : G.Walk u v → ℕ → V
  | nil, _ => u
  | cons _ _, 0 => u
  | cons _ q, n + 1 => q.getVert n

@[simp]
theorem getVert_zero {u v} (w : G.Walk u v) : w.getVert 0 = u := by cases w <;> rfl

@[simp]
theorem getVert_nil (u : V) {i : ℕ} : (@nil _ G u).getVert i = u := rfl

theorem getVert_of_length_le {u v} (w : G.Walk u v) {i : ℕ} (hi : w.length ≤ i) :
    w.getVert i = v := by
  induction w generalizing i with
  | nil => rfl
  | cons _ _ ih =>
    cases i
    · cases hi
    · exact ih (Nat.succ_le_succ_iff.1 hi)

@[simp]
theorem getVert_length {u v} (w : G.Walk u v) : w.getVert w.length = v :=
  w.getVert_of_length_le rfl.le

theorem adj_getVert_succ {u v} (w : G.Walk u v) {i : ℕ} (hi : i < w.length) :
    G.Adj (w.getVert i) (w.getVert (i + 1)) := by
  induction w generalizing i with
  | nil => cases hi
  | cons hxy _ ih =>
    cases i
    · simp [getVert, hxy]
    · exact ih (Nat.succ_lt_succ_iff.1 hi)

@[simp]
lemma getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) :
    (p.cons h).getVert (n + 1) = p.getVert n := rfl

lemma getVert_cons {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n ≠ 0) :
    (p.cons h).getVert n = p.getVert (n - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero hn
  rw [getVert_cons_succ, Nat.add_sub_cancel]

@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) := rfl

@[simp]
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p := rfl

@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

@[simp]
theorem append_nil {u v : V} (p : G.Walk u v) : p.append nil = p := by
  induction p with
  | nil => rw [nil_append]
  | cons _ _ ih => rw [cons_append, ih]

theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    p.append (q.append r) = (p.append q).append r := by
  induction p with
  | nil => rw [nil_append, nil_append]
  | cons h p' ih => rw [cons_append, cons_append, cons_append, ih]

@[simp]
theorem append_copy_copy {u v w u' v' w'} (p : G.Walk u v) (q : G.Walk v w)
    (hu : u = u') (hv : v = v') (hw : w = w') :
    (p.copy hu hv).append (q.copy hv hw) = (p.append q).copy hu hw := by
  subst_vars
  rfl

theorem concat_nil {u v : V} (h : G.Adj u v) : nil.concat h = cons h nil := rfl

@[simp]
theorem concat_cons {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (h' : G.Adj w x) :
    (cons h p).concat h' = cons h (p.concat h') := rfl

theorem append_concat {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (h : G.Adj w x) :
    p.append (q.concat h) = (p.append q).concat h := append_assoc _ _ _

theorem concat_append {u v w x : V} (p : G.Walk u v) (h : G.Adj v w) (q : G.Walk w x) :
    (p.concat h).append q = p.append (cons h q) := by
  rw [concat_eq_append, ← append_assoc, cons_nil_append]

/-- A non-trivial `cons` walk is representable as a `concat` walk. -/
theorem exists_cons_eq_concat {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    ∃ (x : V) (q : G.Walk u x) (h' : G.Adj x w), cons h p = q.concat h' := by
  induction p generalizing u with
  | nil => exact ⟨_, nil, h, rfl⟩
  | cons h' p ih =>
    obtain ⟨y, q, h'', hc⟩ := ih h'
    refine ⟨y, cons h q, h'', ?_⟩
    rw [concat_cons, hc]

/-- A non-trivial `concat` walk is representable as a `cons` walk. -/
theorem exists_concat_eq_cons {u v w : V} :
    ∀ (p : G.Walk u v) (h : G.Adj v w),
      ∃ (x : V) (h' : G.Adj u x) (q : G.Walk x w), p.concat h = cons h' q
  | nil, h => ⟨_, h, nil, rfl⟩
  | cons h' p, h => ⟨_, h', Walk.concat p h, concat_cons _ _ _⟩

@[simp]
theorem reverse_nil {u : V} : (nil : G.Walk u u).reverse = nil := rfl

theorem reverse_singleton {u v : V} (h : G.Adj u v) : (cons h nil).reverse = cons (G.symm h) nil :=
  rfl

@[simp]
theorem cons_reverseAux {u v w x : V} (p : G.Walk u v) (q : G.Walk w x) (h : G.Adj w u) :
    (cons h p).reverseAux q = p.reverseAux (cons (G.symm h) q) := rfl

@[simp]
protected theorem append_reverseAux {u v w x : V}
    (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk u x) :
    (p.append q).reverseAux r = q.reverseAux (p.reverseAux r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => exact ih q (cons (G.symm h) r)

@[simp]
protected theorem reverseAux_append {u v w x : V}
    (p : G.Walk u v) (q : G.Walk u w) (r : G.Walk w x) :
    (p.reverseAux q).append r = p.reverseAux (q.append r) := by
  induction p with
  | nil => rfl
  | cons h _ ih => simp [ih (cons (G.symm h) q)]

protected theorem reverseAux_eq_reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    p.reverseAux q = p.reverse.append q := by simp [reverse]

@[simp]
theorem reverse_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).reverse = p.reverse.append (cons (G.symm h) nil) := by simp [reverse]

@[simp]
theorem reverse_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).reverse = p.reverse.copy hv hu := by
  subst_vars
  rfl

@[simp]
theorem reverse_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).reverse = q.reverse.append p.reverse := by simp [reverse]

@[simp]
theorem reverse_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).reverse = cons (G.symm h) p.reverse := by simp [concat_eq_append]

@[simp]
theorem reverse_reverse {u v : V} (p : G.Walk u v) : p.reverse.reverse = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]

theorem reverse_surjective {u v : V} : Function.Surjective (reverse : G.Walk u v → _) :=
  RightInverse.surjective reverse_reverse

theorem reverse_injective {u v : V} : Function.Injective (reverse : G.Walk u v → _) :=
  RightInverse.injective reverse_reverse

theorem reverse_bijective {u v : V} : Function.Bijective (reverse : G.Walk u v → _) :=
  And.intro reverse_injective reverse_surjective

@[simp]
theorem length_nil {u : V} : (nil : G.Walk u u).length = 0 := rfl

@[simp]
theorem length_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).length = p.length + 1 := rfl

@[simp]
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl

@[simp]
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp [ih, add_comm, add_assoc]

@[simp]
theorem length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = p.length + 1 := length_append _ _

@[simp]
protected theorem length_reverseAux {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    (p.reverseAux q).length = p.length + q.length := by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, Nat.add_assoc]

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]

theorem eq_of_length_eq_zero {u v : V} : ∀ {p : G.Walk u v}, p.length = 0 → u = v
  | nil, _ => rfl

theorem adj_of_length_eq_one {u v : V} : ∀ {p : G.Walk u v}, p.length = 1 → G.Adj u v
  | cons h nil, _ => h

@[simp]
theorem exists_length_eq_zero_iff {u v : V} : (∃ p : G.Walk u v, p.length = 0) ↔ u = v := by
  constructor
  · rintro ⟨p, hp⟩
    exact eq_of_length_eq_zero hp
  · rintro rfl
    exact ⟨nil, rfl⟩

@[simp]
lemma exists_length_eq_one_iff {u v : V} : (∃ (p : G.Walk u v), p.length = 1) ↔ G.Adj u v := by
  refine ⟨?_, fun h ↦ ⟨h.toWalk, by simp⟩⟩
  rintro ⟨p, hp⟩
  induction p with
  | nil => simp only [Walk.length_nil, zero_ne_one] at hp
  | cons h p' =>
    simp only [Walk.length_cons, add_eq_right] at hp
    exact (p'.eq_of_length_eq_zero hp) ▸ h

@[simp]
theorem length_eq_zero_iff {u : V} {p : G.Walk u u} : p.length = 0 ↔ p = nil := by cases p <;> simp

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
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (Nat.sub_pos_of_lt hi') rfl, Nat.sub_eq_zero_of_le hi']
        simp [getVert]

section ConcatRec

variable {motive : ∀ u v : V, G.Walk u v → Sort*} (Hnil : ∀ {u : V}, motive u u nil)
  (Hconcat : ∀ {u v w : V} (p : G.Walk u v) (h : G.Adj v w), motive u v p → motive u w (p.concat h))

/-- Auxiliary definition for `SimpleGraph.Walk.concatRec` -/
def concatRecAux {u v : V} : (p : G.Walk u v) → motive v u p.reverse
  | nil => Hnil
  | cons h p => reverse_cons h p ▸ Hconcat p.reverse h.symm (concatRecAux p)

/-- Recursor on walks by inducting on `SimpleGraph.Walk.concat`.

This is inducting from the opposite end of the walk compared
to `SimpleGraph.Walk.rec`, which inducts on `SimpleGraph.Walk.cons`. -/
@[elab_as_elim]
def concatRec {u v : V} (p : G.Walk u v) : motive u v p :=
  reverse_reverse p ▸ concatRecAux @Hnil @Hconcat p.reverse

@[simp]
theorem concatRec_nil (u : V) :
    @concatRec _ _ motive @Hnil @Hconcat _ _ (nil : G.Walk u u) = Hnil := rfl

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
  · rw [concatRecAux, eqRec_heq_iff_heq]
    congr <;> simp

end ConcatRec

theorem concat_ne_nil {u v : V} (p : G.Walk u v) (h : G.Adj v u) : p.concat h ≠ nil := by
  cases p <;> simp [concat]

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

/-- The `support` of a walk is the list of vertices it visits in order. -/
def support {u v : V} : G.Walk u v → List V
  | nil => [u]
  | cons _ p => u :: p.support

/-- The `darts` of a walk is the list of darts it visits in order. -/
def darts {u v : V} : G.Walk u v → List G.Dart
  | nil => []
  | cons h p => ⟨(u, _), h⟩ :: p.darts

/-- The `edges` of a walk is the list of edges it visits in order.
This is defined to be the list of edges underlying `SimpleGraph.Walk.darts`. -/
def edges {u v : V} (p : G.Walk u v) : List (Sym2 V) := p.darts.map Dart.edge

@[simp]
theorem support_nil {u : V} : (nil : G.Walk u u).support = [u] := rfl

@[simp]
theorem support_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).support = u :: p.support := rfl

@[simp]
theorem support_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).support = p.support.concat w := by
  induction p <;> simp [*, concat_nil]

@[simp]
theorem support_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).support = p.support := by
  subst_vars
  rfl

theorem support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support ++ p'.support.tail := by
  induction p <;> cases p' <;> simp [*]

@[simp]
theorem support_reverse {u v : V} (p : G.Walk u v) : p.reverse.support = p.support.reverse := by
  induction p <;> simp [support_append, *]

@[simp]
theorem support_ne_nil {u v : V} (p : G.Walk u v) : p.support ≠ [] := by cases p <;> simp

theorem support_append_eq_support_dropLast_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support.dropLast ++ p'.support := by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

@[simp]
theorem head_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.head (by simp) = a := by cases p <;> simp

@[simp]
theorem getLast_support {G : SimpleGraph V} {a b : V} (p : G.Walk a b) :
    p.support.getLast (by simp) = b := by
  induction p
  · simp
  · simpa

theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append, List.tail_append_of_ne_nil (support_ne_nil _)]

theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

theorem support_eq_concat {u v : V} (p : G.Walk u v) : p.support = p.support.dropLast.concat v := by
  cases p with
  | nil => rfl
  | cons h p =>
    obtain ⟨_, _, _, hq⟩ := exists_cons_eq_concat h p
    simp [hq]

@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩

theorem mem_support_iff {u v w : V} (p : G.Walk u v) :
    w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by cases p <;> simp

@[simp]
theorem getVert_mem_support {u v : V} (p : G.Walk u v) (i : ℕ) : p.getVert i ∈ p.support := by
  induction p generalizing i with
  | nil => simp
  | cons _ _ hind =>
    cases i
    · simp
    · simp [hind]

theorem mem_support_nil_iff {u v : V} : u ∈ (nil : G.Walk v v).support ↔ u = v := by simp

@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
  rw [tail_support_append, List.mem_append]

@[simp]
theorem end_mem_tail_support_of_ne {u v : V} (h : u ≠ v) (p : G.Walk u v) : v ∈ p.support.tail := by
  obtain ⟨_, _, _, rfl⟩ := exists_eq_cons_of_ne h p
  simp

@[simp, nolint unusedHavesSuffices]
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support := by
  simp only [mem_support_iff, mem_tail_support_append_iff]
  obtain rfl | h := eq_or_ne t v <;> obtain rfl | h' := eq_or_ne t u <;>
    -- this `have` triggers the unusedHavesSuffices linter:
    (try have := h'.symm) <;> simp [*]

theorem support_subset_support_cons {u v w : V} (p : G.Walk v w) (hadj : G.Adj u v) :
    p.support ⊆ (p.cons hadj).support := by
  simp

theorem support_subset_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    p.support ⊆ (p.concat hadj).support := by
  simp

@[simp]
theorem subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
  simp only [Walk.support_append, List.subset_append_left]

@[simp]
theorem subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support := by
  intro h
  simp +contextual only [mem_support_append_iff, or_true, imp_true_iff]

theorem coe_support {u v : V} (p : G.Walk u v) :
    (p.support : Multiset V) = {u} + p.support.tail := by cases p <;> rfl

theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]

theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = p.support + p'.support - {v} := by
  rw [support_append, ← Multiset.coe_add]
  simp only [coe_support]
  rw [add_comm ({v} : Multiset V)]
  simp only [← add_assoc, add_tsub_cancel_right]

theorem isChain_adj_cons_support {u v w : V} (h : G.Adj u v) :
    ∀ (p : G.Walk v w), List.IsChain G.Adj (u :: p.support)
  | nil => .cons_cons h (.singleton _)
  | cons h' p => .cons_cons h (isChain_adj_cons_support h' p)

@[deprecated (since := "2025-09-24")] alias chain_adj_support := isChain_adj_cons_support

theorem isChain_adj_support {u v : V} : ∀ (p : G.Walk u v), List.IsChain G.Adj p.support
  | nil => .singleton _
  | cons h p => isChain_adj_cons_support h p

@[deprecated (since := "2025-09-24")] alias chain'_adj_support := isChain_adj_support

theorem isChain_dartAdj_cons_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) :
    List.IsChain G.DartAdj (d :: p.darts) := by
  induction p generalizing d with
  | nil => exact .singleton _
  | cons h' p ih => exact .cons_cons h (ih rfl)

theorem isChain_dartAdj_darts {u v : V} : ∀ (p : G.Walk u v), List.IsChain G.DartAdj p.darts
  | nil => .nil
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => isChain_dartAdj_cons_darts (by rfl) p

@[deprecated (since := "2025-09-24")] alias chain_dartAdj_darts := isChain_dartAdj_cons_darts
@[deprecated (since := "2025-09-24")] alias chain'_dartAdj_darts := isChain_dartAdj_darts

/-- Every edge in a walk's edge list is an edge of the graph.
It is written in this form (rather than using `⊆`) to avoid unsightly coercions. -/
theorem edges_subset_edgeSet {u v : V} :
    ∀ (p : G.Walk u v) ⦃e : Sym2 V⦄, e ∈ p.edges → e ∈ G.edgeSet
  | cons h' p', e, h => by
    cases h
    · exact h'
    next h' => exact edges_subset_edgeSet p' h'

theorem adj_of_mem_edges {u v x y : V} (p : G.Walk u v) (h : s(x, y) ∈ p.edges) : G.Adj x y :=
  edges_subset_edgeSet p h

@[simp]
theorem darts_nil {u : V} : (nil : G.Walk u u).darts = [] := rfl

@[simp]
theorem darts_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).darts = ⟨(u, v), h⟩ :: p.darts := rfl

@[simp]
theorem darts_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).darts = p.darts.concat ⟨(v, w), h⟩ := by
  induction p <;> simp [*, concat_nil]

@[simp]
theorem darts_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).darts = p.darts := by
  subst_vars
  rfl

@[simp]
theorem darts_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').darts = p.darts ++ p'.darts := by
  induction p <;> simp [*]

@[simp]
theorem darts_reverse {u v : V} (p : G.Walk u v) :
    p.reverse.darts = (p.darts.map Dart.symm).reverse := by
  induction p <;> simp [*]

theorem mem_darts_reverse {u v : V} {d : G.Dart} {p : G.Walk u v} :
    d ∈ p.reverse.darts ↔ d.symm ∈ p.darts := by simp

theorem cons_map_snd_darts {u v : V} (p : G.Walk u v) : (u :: p.darts.map (·.snd)) = p.support := by
  induction p <;> simp! [*]

theorem map_snd_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.snd) = p.support.tail := by
  simpa using congr_arg List.tail (cons_map_snd_darts p)

theorem map_fst_darts_append {u v : V} (p : G.Walk u v) :
    p.darts.map (·.fst) ++ [v] = p.support := by
  induction p <;> simp! [*]

theorem map_fst_darts {u v : V} (p : G.Walk u v) : p.darts.map (·.fst) = p.support.dropLast := by
  simpa! using congr_arg List.dropLast (map_fst_darts_append p)

@[simp]
theorem head_darts_fst {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.darts ≠ []) :
    (p.darts.head hp).fst = a := by
  cases p
  · contradiction
  · simp

@[simp]
theorem getLast_darts_snd {G : SimpleGraph V} {a b : V} (p : G.Walk a b) (hp : p.darts ≠ []) :
    (p.darts.getLast hp).snd = b := by
  rw [← List.getLast_map (f := fun x : G.Dart ↦ x.snd)]
  · simp_rw [p.map_snd_darts, List.getLast_tail, p.getLast_support]
  · simpa

@[simp]
theorem edges_nil {u : V} : (nil : G.Walk u u).edges = [] := rfl

@[simp]
theorem edges_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edges = s(u, v) :: p.edges := rfl

@[simp]
theorem edges_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edges = p.edges.concat s(v, w) := by simp [edges]

@[simp]
theorem edges_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edges = p.edges := by
  subst_vars
  rfl

@[simp]
theorem edges_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').edges = p.edges ++ p'.edges := by simp [edges]

@[simp]
theorem edges_reverse {u v : V} (p : G.Walk u v) : p.reverse.edges = p.edges.reverse := by
  simp [edges, List.map_reverse]

@[simp]
theorem length_support {u v : V} (p : G.Walk u v) : p.support.length = p.length + 1 := by
  induction p <;> simp [*]

@[simp]
theorem length_darts {u v : V} (p : G.Walk u v) : p.darts.length = p.length := by
  induction p <;> simp [*]

@[simp]
theorem length_edges {u v : V} (p : G.Walk u v) : p.edges.length = p.length := by simp [edges]

theorem dart_fst_mem_support_of_mem_darts {u v : V} :
    ∀ (p : G.Walk u v) {d : G.Dart}, d ∈ p.darts → d.fst ∈ p.support
  | cons h p', d, hd => by
    simp only [support_cons, darts_cons, List.mem_cons] at hd ⊢
    rcases hd with (rfl | hd)
    · exact Or.inl rfl
    · exact Or.inr (dart_fst_mem_support_of_mem_darts _ hd)

theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart}
    (h : d ∈ p.darts) : d.snd ∈ p.support := by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm ∈ p.reverse.darts)

theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    t ∈ p.support := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd

theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    u ∈ p.support := by
  rw [Sym2.eq_swap] at he
  exact p.fst_mem_support_of_mem_edges he

theorem darts_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.darts.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [darts_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨fun h' => h.1 (dart_fst_mem_support_of_mem_darts p' h'), ih h.2⟩

theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.edges.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [edges_cons, support_cons, List.nodup_cons] at h ⊢
    exact ⟨fun h' => h.1 (fst_mem_support_of_mem_edges p' h'), ih h.2⟩

lemma getVert_eq_support_getElem {u v : V} {n : ℕ} (p : G.Walk u v) (h : n ≤ p.length) :
    p.getVert n = p.support[n]'(p.length_support ▸ Nat.lt_add_one_of_le h) := by
  cases p with
  | nil => simp
  | cons => cases n with
    | zero => simp
    | succ n =>
      simp_rw [support_cons, getVert_cons _ _ n.zero_ne_add_one.symm, List.getElem_cons]
      exact getVert_eq_support_getElem _ (Nat.sub_le_of_le_add h)

lemma getVert_eq_support_getElem? {u v : V} {n : ℕ} (p : G.Walk u v) (h : n ≤ p.length) :
    some (p.getVert n) = p.support[n]? := by
  rw [getVert_eq_support_getElem p h, ← List.getElem?_eq_getElem]

@[deprecated (since := "2025-06-10")]
alias getVert_eq_support_get? := getVert_eq_support_getElem?

lemma getVert_eq_getD_support {u v : V} (p : G.Walk u v) (n : ℕ) :
    p.getVert n = p.support.getD n v := by
  by_cases h : n ≤ p.length
  · simp [← getVert_eq_support_getElem? p h]
  grind [getVert_of_length_le, length_support]

theorem getVert_comp_val_eq_get_support {u v : V} (p : G.Walk u v) :
    p.getVert ∘ Fin.val = p.support.get := by
  grind [getVert_eq_support_getElem, length_support]

theorem range_getVert_eq_range_support_getElem {u v : V} (p : G.Walk u v) :
    Set.range p.getVert = Set.range p.support.get :=
  Set.ext fun _ ↦ ⟨by grind [Set.range_list_get, getVert_mem_support],
    fun ⟨n, _⟩ ↦ ⟨n, by grind [getVert_eq_support_getElem, length_support]⟩⟩

theorem nodup_tail_support_reverse {u : V} {p : G.Walk u u} :
    p.reverse.support.tail.Nodup ↔ p.support.tail.Nodup := by
  rw [Walk.support_reverse]
  refine List.nodup_tail_reverse p.support ?h
  rw [← getVert_eq_support_getElem? _ (by cutsat), List.getLast?_eq_getElem?,
    ← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; cutsat)]
  aesop

theorem edges_injective {u v : V} : Function.Injective (Walk.edges : G.Walk u v → List (Sym2 V))
  | .nil, .nil, _ => rfl
  | .nil, .cons _ _, h => by simp at h
  | .cons _ _, .nil, h => by simp at h
  | .cons' u v c h₁ w₁, .cons' _ v' _ h₂ w₂, h => by
    have h₃ : u ≠ v' := by rintro rfl; exact G.loopless _ h₂
    obtain ⟨rfl, h₃⟩ : v = v' ∧ w₁.edges = w₂.edges := by simpa [h₁, h₃] using h
    obtain rfl := Walk.edges_injective h₃
    rfl

theorem darts_injective {u v : V} : Function.Injective (Walk.darts : G.Walk u v → List G.Dart) :=
  edges_injective.of_comp

/-- The `Set` of edges of a walk. -/
def edgeSet {u v : V} (p : G.Walk u v) : Set (Sym2 V) := {e | e ∈ p.edges}

@[simp]
lemma mem_edgeSet {u v : V} {p : G.Walk u v} {e : Sym2 V} : e ∈ p.edgeSet ↔ e ∈ p.edges := Iff.rfl

@[simp]
lemma edgeSet_nil (u : V) : (nil : G.Walk u u).edgeSet = ∅ := by ext; simp

@[simp]
lemma edgeSet_reverse {u v : V} (p : G.Walk u v) : p.reverse.edgeSet = p.edgeSet := by ext; simp

@[simp]
theorem edgeSet_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h p).edgeSet = insert s(u, v) p.edgeSet := by ext; simp

@[simp]
theorem edgeSet_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edgeSet = insert s(v, w) p.edgeSet := by ext; simp [or_comm]

theorem edgeSet_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by ext; simp

@[simp]
theorem edgeSet_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edgeSet = p.edgeSet := by ext; simp

theorem coe_edges_toFinset [DecidableEq V] {u v : V} (p : G.Walk u v) :
    (p.edges.toFinset : Set (Sym2 V)) = p.edgeSet := by
  simp [edgeSet]

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

lemma not_nil_iff_lt_length {p : G.Walk v w} : ¬ p.Nil ↔ 0 < p.length := by
  cases p <;> simp

lemma not_nil_iff {p : G.Walk v w} :
    ¬ p.Nil ↔ ∃ (u : V) (h : G.Adj v u) (q : G.Walk u w), p = cons h q := by
  cases p <;> simp [*]

@[simp]
lemma nil_append_iff {p : G.Walk u v} {q : G.Walk v w} : (p.append q).Nil ↔ p.Nil ∧ q.Nil := by
  cases p <;> cases q <;> simp

lemma Nil.append {p : G.Walk u v} {q : G.Walk v w} (hp : p.Nil) (hq : q.Nil) : (p.append q).Nil :=
  by simp [hp, hq]

@[simp]
lemma nil_reverse {p : G.Walk v w} : p.reverse.Nil ↔ p.Nil := by
  cases p <;> simp

/-- A walk with its endpoints defeq is `Nil` if and only if it is equal to `nil`. -/
lemma nil_iff_eq_nil : ∀ {p : G.Walk v v}, p.Nil ↔ p = nil
  | .nil | .cons _ _ => by simp

alias ⟨Nil.eq_nil, _⟩ := nil_iff_eq_nil

/-- The recursion principle for nonempty walks -/
@[elab_as_elim]
def notNilRec {motive : {u w : V} → (p : G.Walk u w) → (h : ¬ p.Nil) → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) → motive (cons h q) not_nil_cons)
    (p : G.Walk u w) : (hp : ¬ p.Nil) → motive p hp :=
  match p with
  | nil => fun hp => absurd .nil hp
  | .cons h q => fun _ => cons h q

@[simp]
lemma notNilRec_cons {motive : {u w : V} → (p : G.Walk u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : G.Adj u v) (q' : G.Walk v w) :
    @Walk.notNilRec _ _ _ _ _ cons _ _ = cons h' q' := by rfl

theorem end_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬ p.Nil) : v ∈ p.support.tail :=
  p.notNilRec (by simp) h

/-- The walk obtained by removing the first `n` darts of a walk. -/
def drop {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

@[simp]
lemma drop_length (p : G.Walk u v) (n : ℕ) : (p.drop n).length = p.length - n := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop]

@[simp]
lemma drop_getVert (p : G.Walk u v) (n m : ℕ) : (p.drop n).getVert m = p.getVert (n + m) := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop, Nat.add_right_comm]

/-- The second vertex of a walk, or the only vertex in a nil walk. -/
abbrev snd (p : G.Walk u v) : V := p.getVert 1

@[simp] lemma adj_snd {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v p.snd := by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)

lemma snd_cons {u v w} (q : G.Walk v w) (hadj : G.Adj u v) :
    (q.cons hadj).snd = v := by simp

/-- The walk obtained by taking the first `n` darts of a walk. -/
def take {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk u (p.getVert n) :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]
lemma take_length (p : G.Walk u v) (n : ℕ) : (p.take n).length = n ⊓ p.length := by
  induction p generalizing n with
  | nil => simp [take]
  | cons => cases n <;> simp_all [take]

@[simp]
lemma take_getVert (p : G.Walk u v) (n m : ℕ) : (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m with
  | nil => simp [take]
  | cons => cases n <;> cases m <;> simp_all [take]

lemma take_support_eq_support_take_succ {u v} (p : G.Walk u v) (n : ℕ) :
    (p.take n).support = p.support.take (n + 1) := by
  induction p generalizing n with
  | nil => simp [take]
  | cons => cases n <;> simp_all [take]

/-- The penultimate vertex of a walk, or the only vertex in a nil walk. -/
abbrev penultimate (p : G.Walk u v) : V := p.getVert (p.length - 1)

@[simp]
lemma penultimate_nil : (@nil _ G v).penultimate = v := rfl

@[simp]
lemma penultimate_cons_nil (h : G.Adj u v) : (cons h nil).penultimate = u := rfl

@[simp]
lemma penultimate_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).penultimate = (cons h₂ p).penultimate := rfl

lemma penultimate_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).penultimate = p.penultimate :=
  p.notNilRec (by simp) hp h

@[simp]
lemma penultimate_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).penultimate = v := by simp [penultimate, concat_eq_append, getVert_append]

@[simp]
lemma adj_penultimate {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj p.penultimate w := by
  conv => rhs; rw [← getVert_length p]
  rw [nil_iff_length_eq] at hp
  convert adj_getVert_succ _ _ <;> omega

@[simp]
lemma snd_reverse (p : G.Walk u v) : p.reverse.snd = p.penultimate := by
  simpa using getVert_reverse p 1

@[simp]
lemma penultimate_reverse (p : G.Walk u v) : p.reverse.penultimate = p.snd := by
  cases p <;> simp [snd, penultimate, getVert_append]

/-- The walk obtained by removing the first dart of a walk. A nil walk stays nil. -/
def tail (p : G.Walk u v) : G.Walk (p.snd) v := p.drop 1

lemma drop_zero {u v} (p : G.Walk u v) :
    p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [Walk.drop]

lemma drop_support_eq_support_drop_min {u v} (p : G.Walk u v) (n : ℕ) :
    (p.drop n).support = p.support.drop (n ⊓ p.length) := by
  induction p generalizing n with
  | nil => simp [drop]
  | cons => cases n <;> simp_all [drop]

/-- The walk obtained by removing the last dart of a walk. A nil walk stays nil. -/
def dropLast (p : G.Walk u v) : G.Walk u p.penultimate := p.take (p.length - 1)

@[simp]
lemma tail_nil : (@nil _ G v).tail = .nil := rfl

@[simp]
lemma tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil := rfl

@[simp]
lemma tail_cons (h : G.Adj u v) (p : G.Walk v w) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  match p with
  | .nil => rfl
  | .cons h q => rfl

@[deprecated (since := "2025-08-19")] alias tail_cons_eq := tail_cons

@[simp]
lemma dropLast_nil : (@nil _ G v).dropLast = nil := rfl

@[simp]
lemma dropLast_cons_nil (h : G.Adj u v) : (cons h nil).dropLast = nil := rfl

@[simp]
lemma dropLast_cons_cons {w'} (h : G.Adj u v) (h₂ : G.Adj v w) (p : G.Walk w w') :
    (cons h (cons h₂ p)).dropLast = cons h (cons h₂ p).dropLast := rfl

lemma dropLast_cons_of_not_nil (h : G.Adj u v) (p : G.Walk v w) (hp : ¬ p.Nil) :
    (cons h p).dropLast = cons h (p.dropLast.copy rfl (penultimate_cons_of_not_nil _ _ hp).symm) :=
  p.notNilRec (by simp) hp h

@[simp]
lemma dropLast_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).dropLast = p.copy rfl (by simp) := by
  induction p
  · rfl
  · simp_rw [concat_cons]
    rw [dropLast_cons_of_not_nil]
    · simp [*]
    · simp [concat, nil_iff_length_eq]

/-- The first dart of a walk. -/
@[simps]
def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := v
  snd := p.snd
  adj := p.adj_snd hp

/-- The last dart of a walk. -/
@[simps]
def lastDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := p.penultimate
  snd := w
  adj := p.adj_penultimate hp

lemma edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.firstDart hp).edge = s(v, p.snd) := rfl

lemma edge_lastDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.lastDart hp).edge = s(p.penultimate, w) := rfl

lemma cons_tail_eq (p : G.Walk u v) (hp : ¬ p.Nil) :
    cons (p.adj_snd hp) p.tail = p := by
  cases p with
  | nil => simp at hp
  | cons h q =>
    simp only [getVert_cons_succ, tail_cons, cons_copy, copy_rfl_rfl]

@[simp]
lemma concat_dropLast (p : G.Walk u v) (hp : G.Adj p.penultimate v) :
    p.dropLast.concat hp = p := by
  induction p with
  | nil => simp at hp
  | cons hadj p hind =>
    cases p with
    | nil => rfl
    | _ => simp [hind]

@[simp] lemma cons_support_tail (p : G.Walk u v) (hp : ¬p.Nil) :
    u :: p.tail.support = p.support := by
  rw [← support_cons (p.adj_snd hp), cons_tail_eq _ hp]

@[simp] lemma length_tail_add_one {p : G.Walk u v} (hp : ¬ p.Nil) :
    p.tail.length + 1 = p.length := by
  rw [← length_cons (p.adj_snd hp), cons_tail_eq _ hp]

protected lemma Nil.tail {p : G.Walk v w} (hp : p.Nil) : p.tail.Nil := by cases p <;> aesop

lemma not_nil_of_tail_not_nil {p : G.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil := mt Nil.tail hp

@[simp] lemma nil_copy {u' v' : V} {p : G.Walk u v} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).Nil = p.Nil := by
  subst_vars; rfl

@[simp] lemma support_tail (p : G.Walk u u) (hp : ¬ p.Nil) :
    p.tail.support = p.support.tail := by
  rw [← cons_support_tail p hp, List.tail_cons]

lemma support_tail_of_not_nil (p : G.Walk u v) (hnp : ¬p.Nil) :
    p.tail.support = p.support.tail := by
  match p with
  | .nil => simp only [nil_nil, not_true_eq_false] at hnp
  | .cons h q =>
    simp only [tail_cons, getVert_cons_succ, support_copy, support_cons, List.tail_cons]

/-- Given a set `S` and a walk `w` from `u` to `v` such that `u ∈ S` but `v ∉ S`,
there exists a dart in the walk whose start is in `S` but whose end is not. -/
theorem exists_boundary_dart {u v : V} (p : G.Walk u v) (S : Set V) (uS : u ∈ S) (vS : v ∉ S) :
    ∃ d : G.Dart, d ∈ p.darts ∧ d.fst ∈ S ∧ d.snd ∉ S := by
  induction p with
  | nil => cases vS uS
  | cons a p' ih =>
    rename_i x y w
    by_cases h : y ∈ S
    · obtain ⟨d, hd, hcd⟩ := ih h vS
      exact ⟨d, List.Mem.tail _ hd, hcd⟩
    · exact ⟨⟨(x, y), a⟩, List.Mem.head _, uS, h⟩

@[simp] lemma getVert_copy {u v w x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  rfl

@[simp] lemma getVert_tail {u v n} (p : G.Walk u v) :
    p.tail.getVert n = p.getVert (n + 1) := by
  match p with
  | .nil => rfl
  | .cons h q =>
    simp only [getVert_cons_succ, tail_cons]
    exact getVert_copy q n (getVert_zero q).symm rfl

lemma ext_support {u v} {p q : G.Walk u v} (h : p.support = q.support) :
    p = q := by
  induction q with
  | nil =>
    rw [← nil_iff_eq_nil, nil_iff_support_eq]
    exact support_nil ▸ h
  | cons ha q ih =>
    cases p with
    | nil => simp at h
    | cons _ p =>
      simp only [support_cons, List.cons.injEq, true_and] at h
      apply List.getElem_of_eq at h
      specialize h (i := 0) (by simp)
      rw [List.getElem_zero, List.getElem_zero, p.head_support, q.head_support] at h
      have : (p.copy h rfl).support = q.support := by simpa
      simp [← ih this]

lemma support_injective {u v : V} : (support (G := G) (u := u) (v := v)).Injective :=
  fun _ _ ↦ ext_support

lemma ext_getVert_le_length {u v} {p q : G.Walk u v} (hl : p.length = q.length)
    (h : ∀ k ≤ p.length, p.getVert k = q.getVert k) :
    p = q := by
  suffices ∀ k : ℕ, p.support[k]? = q.support[k]? by
    exact ext_support <| List.ext_getElem?_iff.mpr this
  intro k
  cases le_or_gt k p.length with
  | inl hk =>
    rw [← getVert_eq_support_getElem? p hk, ← getVert_eq_support_getElem? q (hl ▸ hk)]
    exact congrArg some (h k hk)
  | inr hk =>
    replace hk : p.length + 1 ≤ k := hk
    have ht : q.length + 1 ≤ k := hl ▸ hk
    rw [← length_support, ← List.getElem?_eq_none_iff] at hk ht
    rw [hk, ht]

lemma ext_getVert {u v} {p q : G.Walk u v} (h : ∀ k, p.getVert k = q.getVert k) :
    p = q := by
  wlog hpq : p.length ≤ q.length generalizing p q
  · exact (this (fun k ↦ (h k).symm) (le_of_not_ge hpq)).symm
  have : q.length ≤ p.length := by
    by_contra!
    exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])
  exact ext_getVert_le_length (hpq.antisymm this) fun k _ ↦ h k

end Walk

/-! ### Mapping walks -/

namespace Walk

variable {G G' G''}

/-- Given a graph homomorphism, map walks to walks. -/
protected def map (f : G →g G') {u v : V} : G.Walk u v → G'.Walk (f u) (f v)
  | nil => nil
  | cons h p => cons (f.map_adj h) (p.map f)

variable (f : G →g G') (f' : G' →g G'') {u v u' v' : V} (p : G.Walk u v)

@[simp]
theorem map_nil : (nil : G.Walk u u).map f = nil := rfl

@[simp]
theorem map_cons {w : V} (h : G.Adj w u) : (cons h p).map f = cons (f.map_adj h) (p.map f) := rfl

@[simp]
theorem map_copy (hu : u = u') (hv : v = v') :
    (p.copy hu hv).map f = (p.map f).copy (hu ▸ rfl) (hv ▸ rfl) := by
  subst_vars
  rfl

@[simp]
theorem map_id (p : G.Walk u v) : p.map Hom.id = p := by
  induction p with
  | nil => rfl
  | cons _ p' ih => simp [ih]

@[simp]
theorem map_map : (p.map f).map f' = p.map (f'.comp f) := by
  induction p with
  | nil => rfl
  | cons _ _ ih => simp [ih]

/-- Unlike categories, for graphs vertex equality is an important notion, so needing to be able to
work with equality of graph homomorphisms is a necessary evil. -/
theorem map_eq_of_eq {f : G →g G'} (f' : G →g G') (h : f = f') :
    p.map f = (p.map f').copy (h ▸ rfl) (h ▸ rfl) := by
  subst_vars
  rfl

@[simp]
theorem map_eq_nil_iff {p : G.Walk u u} : p.map f = nil ↔ p = nil := by cases p <;> simp

@[simp]
theorem length_map : (p.map f).length = p.length := by induction p <;> simp [*]

theorem map_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).map f = (p.map f).append (q.map f) := by induction p <;> simp [*]

@[simp]
theorem reverse_map : (p.map f).reverse = p.reverse.map f := by induction p <;> simp [map_append, *]

@[simp]
theorem support_map : (p.map f).support = p.support.map f := by induction p <;> simp [*]

@[simp]
theorem darts_map : (p.map f).darts = p.darts.map f.mapDart := by induction p <;> simp [*]

@[simp]
theorem edges_map : (p.map f).edges = p.edges.map (Sym2.map f) := by
  induction p with
  | nil => rfl
  | cons _ _ ih =>
    simp only [Walk.map_cons, edges_cons, List.map_cons, Sym2.map_pair_eq,
      ih]

@[simp]
theorem edgeSet_map : (p.map f).edgeSet = Sym2.map f '' p.edgeSet := by ext; simp

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
      simp only [cons.injEq, heq_iff_eq, true_and]
      apply ih
      simpa using h.2

/-- The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs. -/
abbrev mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v) : G'.Walk u v :=
  p.map (.ofLE h)

/-! ### Transferring between graphs -/

/-- The walk `p` transferred to lie in `H`, given that `H` contains its edges. -/
@[simp]
protected def transfer {u v : V} (p : G.Walk u v)
    (H : SimpleGraph V) (h : ∀ e, e ∈ p.edges → e ∈ H.edgeSet) : H.Walk u v :=
  match p with
  | nil => nil
  | cons' u v w _ p =>
    cons (h s(u, v) (by simp)) (p.transfer H fun e he => h e (by simp [he]))

variable {u v : V} (p : G.Walk u v)

theorem transfer_self : p.transfer G p.edges_subset_edgeSet = p := by
  induction p <;> simp [*]

variable {H : SimpleGraph V}

theorem transfer_eq_map_ofLE (hp) (GH : G ≤ H) : p.transfer H hp = p.map (.ofLE GH) := by
  induction p <;> simp [*]

@[deprecated (since := "2025-03-17")] alias transfer_eq_map_of_le := transfer_eq_map_ofLE

@[simp]
theorem edges_transfer (hp) : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp [*]

@[simp]
theorem edgeSet_transfer (hp) : (p.transfer H hp).edgeSet = p.edgeSet := by ext; simp

@[simp]
theorem support_transfer (hp) : (p.transfer H hp).support = p.support := by
  induction p <;> simp [*]

@[simp]
theorem length_transfer (hp) : (p.transfer H hp).length = p.length := by
  induction p <;> simp [*]

@[simp]
theorem transfer_transfer (hp) {K : SimpleGraph V} (hp') :
    (p.transfer H hp).transfer K hp' = p.transfer K (p.edges_transfer hp ▸ hp') := by
  induction p with
  | nil => simp
  | cons _ _ ih =>
    simp only [Walk.transfer, cons.injEq, heq_eq_eq, true_and]
    apply ih

@[simp]
theorem transfer_append {w : V} (q : G.Walk v w) (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => hpq _ (by simp [he])).append
        (q.transfer H fun e he => hpq _ (by simp [he])) := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp only [Walk.transfer, cons_append, ih]

@[simp]
theorem reverse_transfer (hp) :
    (p.transfer H hp).reverse =
      p.reverse.transfer H (by simp only [edges_reverse, List.mem_reverse]; exact hp) := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp only [transfer_append, Walk.transfer, reverse_cons, ih]

/-! ### Inducing a walk -/

variable {s : Set V}

variable (s) in
/-- A walk in `G` which is fully contained in a set `s` of vertices lifts to a walk of `G[s]`. -/
protected def induce {u v : V} :
    ∀ (w : G.Walk u v) (hw : ∀ x ∈ w.support, x ∈ s),
      (G.induce s).Walk ⟨u, hw _ w.start_mem_support⟩ ⟨v, hw _ w.end_mem_support⟩
  | .nil, hw => .nil
  | .cons (v := u') huu' w, hw => .cons (induce_adj.2 huu') <| w.induce <| by simp_all

@[simp] lemma induce_nil (hw) : (.nil : G.Walk u u).induce s hw = .nil := rfl

@[simp] lemma induce_cons (huu' : G.Adj u u') (w : G.Walk u' v) (hw) :
    (w.cons huu').induce s hw = .cons (induce_adj.2 huu') (w.induce s <| by simp_all) := rfl

@[simp] lemma support_induce {u v : V} :
    ∀ (w : G.Walk u v) (hw), (w.induce s hw).support = w.support.attachWith _ hw
  | .nil, hw => rfl
  | .cons (v := u') hu w, hw => by simp [support_induce]

@[simp] lemma map_induce {u v : V} :
    ∀ (w : G.Walk u v) (hw), (w.induce s hw).map (Embedding.induce _).toHom = w
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce]

lemma map_induce_induceHomOfLE {s s' : Set V} (hs : s ⊆ s') {u v : V} : ∀ (w : G.Walk u v) (hw),
    (w.induce s hw).map (G.induceHomOfLE hs).toHom = w.induce s' (subset_trans hw hs)
  | .nil, hw => rfl
  | .cons (v := u') huu' w, hw => by simp [map_induce_induceHomOfLE]

end Walk

/-! ## Deleting edges -/

namespace Walk

variable {G}

/-- Given a walk that avoids a set of edges, produce a walk in the graph
with those edges deleted. -/
abbrev toDeleteEdges (s : Set (Sym2 V)) {v w : V} (p : G.Walk v w)
    (hp : ∀ e, e ∈ p.edges → e ∉ s) : (G.deleteEdges s).Walk v w :=
  p.transfer _ <| by
    simp only [edgeSet_deleteEdges, Set.mem_diff]
    exact fun e ep => ⟨edges_subset_edgeSet p ep, hp e ep⟩

@[simp]
theorem toDeleteEdges_nil (s : Set (Sym2 V)) {v : V} (hp) :
    (Walk.nil : G.Walk v v).toDeleteEdges s hp = Walk.nil := rfl

@[simp]
theorem toDeleteEdges_cons (s : Set (Sym2 V)) {u v w : V} (h : G.Adj u v) (p : G.Walk v w) (hp) :
    (Walk.cons h p).toDeleteEdges s hp =
      Walk.cons (deleteEdges_adj.mpr ⟨h, hp _ (List.Mem.head _)⟩)
        (p.toDeleteEdges s fun _ he => hp _ <| List.Mem.tail _ he) :=
  rfl

variable {v w : V}

/-- Given a walk that avoids an edge, create a walk in the subgraph with that edge deleted.
This is an abbreviation for `SimpleGraph.Walk.toDeleteEdges`. -/
abbrev toDeleteEdge (e : Sym2 V) (p : G.Walk v w) (hp : e ∉ p.edges) :
    (G.deleteEdges {e}).Walk v w :=
  p.toDeleteEdges {e} (fun e' => by contrapose!; simp +contextual [hp])

@[simp]
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : G.Walk v w} (hp) :
    Walk.map (.ofLE (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_ofLE, transfer_transfer, transfer_self]
  intro e
  rw [edges_transfer]
  apply edges_subset_edgeSet p

end Walk

/-! ## Subwalks -/

namespace Walk

variable {V : Type*} {G : SimpleGraph V}

/-- `p.IsSubwalk q` means that the walk `p` is a contiguous subwalk of the walk `q`. -/
def IsSubwalk {u₁ v₁ u₂ v₂} (p : G.Walk u₁ v₁) (q : G.Walk u₂ v₂) : Prop :=
  ∃ (ru : G.Walk u₂ u₁) (rv : G.Walk v₁ v₂), q = (ru.append p).append rv

@[refl, simp]
lemma isSubwalk_rfl {u v} (p : G.Walk u v) : p.IsSubwalk p :=
  ⟨nil, nil, by simp⟩

@[simp]
lemma nil_isSubwalk {u v} (q : G.Walk u v) : (Walk.nil : G.Walk u u).IsSubwalk q :=
  ⟨nil, q, by simp⟩

protected lemma IsSubwalk.cons {u v u' v' w} {p : G.Walk u v} {q : G.Walk u' v'}
    (hpq : p.IsSubwalk q) (h : G.Adj w u') : p.IsSubwalk (q.cons h) := by
  obtain ⟨r1, r2, rfl⟩ := hpq
  use r1.cons h, r2
  simp

@[simp]
lemma isSubwalk_cons {u v w} (p : G.Walk u v) (h : G.Adj w u) : p.IsSubwalk (p.cons h) :=
  (isSubwalk_rfl p).cons h

lemma IsSubwalk.trans {u₁ v₁ u₂ v₂ u₃ v₃} {p₁ : G.Walk u₁ v₁} {p₂ : G.Walk u₂ v₂}
    {p₃ : G.Walk u₃ v₃} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₃) :
    p₁.IsSubwalk p₃ := by
  obtain ⟨q₁, r₁, rfl⟩ := h₁
  obtain ⟨q₂, r₂, rfl⟩ := h₂
  use q₂.append q₁, r₁.append r₂
  simp only [append_assoc]

lemma isSubwalk_nil_iff {u v u'} (p : G.Walk u v) :
    p.IsSubwalk (nil : G.Walk u' u') ↔ ∃ (hu : u' = u) (hv : u' = v), p = nil.copy hu hv := by
  cases p with
  | nil =>
    constructor
    · rintro ⟨_ | _, _, ⟨⟩⟩
      simp
    · rintro ⟨rfl, _, _⟩
      simp
  | cons h p =>
    constructor
    · rintro ⟨_ | _, _, h⟩ <;> simp at h
    · rintro ⟨rfl, rfl, ⟨⟩⟩

lemma nil_isSubwalk_iff_exists {u' u v} (q : G.Walk u v) :
    (Walk.nil : G.Walk u' u').IsSubwalk q ↔
      ∃ (ru : G.Walk u u') (rv : G.Walk u' v), q = ru.append rv := by
  simp [IsSubwalk]

lemma length_le_of_isSubwalk {u₁ v₁ u₂ v₂} {q : G.Walk u₁ v₁} {p : G.Walk u₂ v₂}
    (h : p.IsSubwalk q) : p.length ≤ q.length := by
  grind [IsSubwalk, length_append]

lemma isSubwalk_of_append_left {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₁.IsSubwalk p₃ :=
  ⟨nil, p₂, h⟩

lemma isSubwalk_of_append_right {v w u : V} {p₁ : G.Walk v w} {p₂ : G.Walk w u} {p₃ : G.Walk v u}
    (h : p₃ = p₁.append p₂) : p₂.IsSubwalk p₃ :=
  ⟨p₁, nil, append_nil _ ▸ h⟩

theorem isSubwalk_iff_support_isInfix {v w v' w' : V} {p₁ : G.Walk v w} {p₂ : G.Walk v' w'} :
    p₁.IsSubwalk p₂ ↔ p₁.support <:+: p₂.support := by
  refine ⟨fun ⟨ru, rv, h⟩ ↦ ?_, fun ⟨s, t, h⟩ ↦ ?_⟩
  · grind [support_append, support_append_eq_support_dropLast_append]
  · have : (s.length + p₁.length) ≤ p₂.length := by grind [_=_ length_support]
    have h₁ : p₂.getVert s.length = v := by
      simp [p₂.getVert_eq_support_getElem (by cutsat : s.length ≤ p₂.length), ← h,
        List.getElem_zero]
    have h₂ : p₂.getVert (s.length + p₁.length) = w := by
      simp [p₂.getVert_eq_support_getElem (by omega), ← h,
        ← p₁.getVert_eq_support_getElem (Nat.le_refl _)]
    refine ⟨p₂.take s.length |>.copy rfl h₁, p₂.drop (s.length + p₁.length) |>.copy h₂ rfl, ?_⟩
    apply ext_support
    simp only [← h, support_append, support_copy, take_support_eq_support_take_succ,
      List.take_append, drop_support_eq_support_drop_min, List.tail_drop]
    rw [Nat.min_eq_left (by grind [length_support]), List.drop_append, List.drop_append,
      List.drop_eq_nil_of_le (by cutsat), List.drop_eq_nil_of_le (by grind [length_support]),
      p₁.support_eq_cons]
    simp +arith

lemma isSubwalk_antisymm {u v} {p₁ p₂ : G.Walk u v} (h₁ : p₁.IsSubwalk p₂) (h₂ : p₂.IsSubwalk p₁) :
    p₁ = p₂ := by
  rw [isSubwalk_iff_support_isInfix] at h₁ h₂
  exact ext_support <| List.infix_antisymm h₁ h₂

end Walk

end SimpleGraph

/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.List.Lemmas

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

lemma getVert_cons_one {u v w} (q : G.Walk v w) (hadj : G.Adj u v) :
    (q.cons hadj).getVert 1 = v := by
  have : (q.cons hadj).getVert 1 = q.getVert 0 := rfl
  simpa [getVert_zero] using this

@[simp]
lemma getVert_cons_succ {u v w n} (p : G.Walk v w) (h : G.Adj u v) :
    (p.cons h).getVert (n + 1) = p.getVert n := rfl

lemma getVert_cons {u v w n} (p : G.Walk v w) (h : G.Adj u v) (hn : n ≠ 0) :
    (p.cons h).getVert n = p.getVert (n - 1) := by
  obtain ⟨i, hi⟩ : ∃ (i : ℕ), i.succ = n := by
    use n - 1; exact Nat.succ_pred_eq_of_ne_zero hn
  rw [← hi]
  simp only [Nat.succ_eq_add_one, getVert_cons_succ, Nat.add_sub_cancel]

@[simp]
theorem cons_append {u v w x : V} (h : G.Adj u v) (p : G.Walk v w) (q : G.Walk w x) :
    (cons h p).append q = cons h (p.append q) := rfl

@[simp]
theorem cons_nil_append {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    (cons h nil).append p = cons h p := rfl

@[simp]
theorem append_nil {u v : V} (p : G.Walk u v) : p.append nil = p := by
  induction p with
  | nil => rfl
  | cons _ _ ih => rw [cons_append, ih]

@[simp]
theorem nil_append {u v : V} (p : G.Walk u v) : nil.append p = p :=
  rfl

theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    p.append (q.append r) = (p.append q).append r := by
  induction p with
  | nil => rfl
  | cons h p' ih =>
    dsimp only [append]
    rw [ih]

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
  | cons _ _ ih => simp [ih, add_comm, add_left_comm, add_assoc]

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
  · rw [concatRecAux, rec_heq_iff_heq]
    congr <;> simp [heq_rec_iff_heq]

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
  rw [support_append, List.tail_append_of_ne_nil _ _ (support_ne_nil _)]

theorem support_eq_cons {u v : V} (p : G.Walk u v) : p.support = u :: p.support.tail := by
  cases p <;> simp

@[simp]
theorem start_mem_support {u v : V} (p : G.Walk u v) : u ∈ p.support := by cases p <;> simp

@[simp]
theorem end_mem_support {u v : V} (p : G.Walk u v) : v ∈ p.support := by induction p <;> simp [*]

@[simp]
theorem support_nonempty {u v : V} (p : G.Walk u v) : { w | w ∈ p.support }.Nonempty :=
  ⟨u, by simp⟩

theorem mem_support_iff {u v w : V} (p : G.Walk u v) :
    w ∈ p.support ↔ w = u ∨ w ∈ p.support.tail := by cases p <;> simp

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

@[simp]
theorem subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
  simp only [Walk.support_append, List.subset_append_left]

@[simp]
theorem subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support := by
  intro h
  simp (config := { contextual := true }) only [mem_support_append_iff, or_true_iff, imp_true_iff]

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

theorem chain_adj_support {u v w : V} (h : G.Adj u v) :
    ∀ (p : G.Walk v w), List.Chain G.Adj u p.support
  | nil => List.Chain.cons h List.Chain.nil
  | cons h' p => List.Chain.cons h (chain_adj_support h' p)

theorem chain'_adj_support {u v : V} : ∀ (p : G.Walk u v), List.Chain' G.Adj p.support
  | nil => List.Chain.nil
  | cons h p => chain_adj_support h p

theorem chain_dartAdj_darts {d : G.Dart} {v w : V} (h : d.snd = v) (p : G.Walk v w) :
    List.Chain G.DartAdj d p.darts := by
  induction p generalizing d with
  | nil => exact List.Chain.nil
  -- Porting note: needed to defer `h` and `rfl` to help elaboration
  | cons h' p ih => exact List.Chain.cons (by exact h) (ih (by rfl))

theorem chain'_dartAdj_darts {u v : V} : ∀ (p : G.Walk u v), List.Chain' G.DartAdj p.darts
  | nil => trivial
  -- Porting note: needed to defer `rfl` to help elaboration
  | cons h p => chain_dartAdj_darts (by rfl) p

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
  induction p <;> simp [*, Sym2.eq_swap]

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
  simp_rw [p.map_snd_darts, List.getLast_tail]
  exact p.getLast_support
  simpa

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

@[simp]
lemma notNilRec_cons {motive : {u w : V} → (p : G.Walk u w) → ¬ p.Nil → Sort*}
    (cons : {u v w : V} → (h : G.Adj u v) → (q : G.Walk v w) →
    motive (q.cons h) Walk.not_nil_cons) (h' : G.Adj u v) (q' : G.Walk v w) :
    @Walk.notNilRec _ _ _ _ _ cons _ _ = cons h' q' := by rfl

@[simp] lemma adj_getVert_one {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v (p.getVert 1) := by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)

/-- The walk obtained by removing the first `n` darts of a walk. -/
def drop {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons h q, (n + 1) => (q.drop n).copy (getVert_cons_succ _ h).symm rfl

/-- The walk obtained by removing the first dart of a non-nil walk. -/
def tail (p : G.Walk u v) : G.Walk (p.getVert 1) v := p.drop 1

@[simp]
lemma tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil := by rfl

lemma tail_cons_eq (h : G.Adj u v) (p : G.Walk v w) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  match p with
  | .nil => rfl
  | .cons h q => rfl

/-- The first dart of a walk. -/
@[simps]
def firstDart (p : G.Walk v w) (hp : ¬ p.Nil) : G.Dart where
  fst := v
  snd := p.getVert 1
  adj := p.adj_getVert_one hp

lemma edge_firstDart (p : G.Walk v w) (hp : ¬ p.Nil) :
    (p.firstDart hp).edge = s(v, p.getVert 1) := rfl

variable {x y : V} -- TODO: rename to u, v, w instead?

lemma cons_tail_eq (p : G.Walk x y) (hp : ¬ p.Nil) :
    cons (p.adj_getVert_one hp) p.tail = p := by
  cases p with
  | nil => simp only [nil_nil, not_true_eq_false] at hp
  | cons h q =>
    simp only [getVert_cons_succ, tail_cons_eq, cons_copy, copy_rfl_rfl]

@[simp] lemma cons_support_tail (p : G.Walk x y) (hp : ¬p.Nil) :
    x :: p.tail.support = p.support := by
  rw [← support_cons, cons_tail_eq _ hp]

@[simp] lemma length_tail_add_one {p : G.Walk x y} (hp : ¬ p.Nil) :
    p.tail.length + 1 = p.length := by
  rw [← length_cons, cons_tail_eq _ hp]

@[simp] lemma nil_copy {x' y' : V} {p : G.Walk x y} (hx : x = x') (hy : y = y') :
    (p.copy hx hy).Nil = p.Nil := by
  subst_vars; rfl

@[simp] lemma support_tail (p : G.Walk v v) (hp : ¬ p.Nil) :
    p.tail.support = p.support.tail := by
  rw [← cons_support_tail p hp, List.tail_cons]

@[simp]
lemma tail_cons {t u v} (p : G.Walk u v) (h : G.Adj t u) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  match p with
  | .nil => rfl
  | .cons h q => rfl

lemma support_tail_of_not_nil (p : G.Walk u v) (hnp : ¬p.Nil) :
    p.tail.support = p.support.tail := by
  match p with
  | .nil => simp only [nil_nil, not_true_eq_false] at hnp
  | .cons h q =>
    simp only [tail_cons, getVert_cons_succ, support_copy, support_cons, List.tail_cons]

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

theorem mem_support_iff_exists_append {V : Type u} {G : SimpleGraph V} {u v w : V}
    {p : G.Walk u v} : w ∈ p.support ↔ ∃ (q : G.Walk u w) (r : G.Walk w v), p = q.append r := by
  classical
  constructor
  · exact fun h => ⟨_, _, (p.take_spec h).symm⟩
  · rintro ⟨q, r, rfl⟩
    simp only [mem_support_append_iff, end_mem_support, start_mem_support, or_self_iff]

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
        · simp only [beq_iff_eq, Sym2.eq, Sym2.rel_iff'] at h''
          obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := h''
          · exact (h' rfl).elim
          · cases p' <;> simp!
        · apply ih

@[simp]
theorem takeUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).takeUntil u h = (p.takeUntil u (by subst_vars; exact h)).copy hv rfl := by
  subst_vars
  rfl

@[simp]
theorem dropUntil_copy {u v w v' w'} (p : G.Walk v w) (hv : v = v') (hw : w = w')
    (h : u ∈ (p.copy hv hw).support) :
    (p.copy hv hw).dropUntil u h = (p.dropUntil u (by subst_vars; exact h)).copy rfl hw := by
  subst_vars
  rfl

theorem support_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inl hx

theorem support_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).support ⊆ p.support := fun x hx => by
  rw [← take_spec p h, mem_support_append_iff]
  exact Or.inr hx

theorem darts_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inl hx

theorem darts_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).darts ⊆ p.darts := fun x hx => by
  rw [← take_spec p h, darts_append, List.mem_append]
  exact Or.inr hx

theorem edges_takeUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_takeUntil_subset h)

theorem edges_dropUntil_subset {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).edges ⊆ p.edges :=
  List.map_subset _ (p.darts_dropUntil_subset h)

theorem length_takeUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.takeUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append] at this
  exact Nat.le.intro this

theorem length_dropUntil_le {u v w : V} (p : G.Walk v w) (h : u ∈ p.support) :
    (p.dropUntil u h).length ≤ p.length := by
  have := congr_arg Walk.length (p.take_spec h)
  rw [length_append, add_comm] at this
  exact Nat.le.intro this

/-- Rotate a loop walk such that it is centered at the given vertex. -/
def rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) : G.Walk u u :=
  (c.dropUntil u h).append (c.takeUntil u h)

@[simp]
theorem support_rotate {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).support.tail ~r c.support.tail := by
  simp only [rotate, tail_support_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← tail_support_append, take_spec]

theorem rotate_darts {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).darts ~r c.darts := by
  simp only [rotate, darts_append]
  apply List.IsRotated.trans List.isRotated_append
  rw [← darts_append, take_spec]

theorem rotate_edges {u v : V} (c : G.Walk v v) (h : u ∈ c.support) :
    (c.rotate h).edges ~r c.edges :=
  (rotate_darts c h).map _

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

@[simp] lemma getVert_copy  {u v w x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  match p, i with
  | .nil, _ =>
    rw [getVert_of_length_le _ (by simp only [length_nil, Nat.zero_le] : nil.length ≤ _)]
    rw [getVert_of_length_le _ (by simp only [length_copy, length_nil, Nat.zero_le])]
  | .cons hadj q, 0 => simp only [copy_rfl_rfl, getVert_zero]
  | .cons hadj q, (n + 1) => simp only [copy_cons, getVert_cons_succ]; rfl

@[simp] lemma getVert_tail {u v n} (p : G.Walk u v) (hnp: ¬ p.Nil) :
    p.tail.getVert n = p.getVert (n + 1) := by
  match p with
  | .nil => rfl
  | .cons h q =>
    simp only [getVert_cons_succ, tail_cons_eq, getVert_cons]
    exact getVert_copy q n (getVert_zero q).symm rfl

/-- Given a walk `w` and a node in the support, there exists a natural `n`, such that given node
is the `n`-th node (zero-indexed) in the walk. In addition, `n` is at most the length of the path.
Due to the definition of `getVert` it would otherwise be legal to return a larger `n` for the last
node. -/
theorem mem_support_iff_exists_getVert {u v w : V} {p : G.Walk v w} :
    u ∈ p.support ↔ ∃ n, p.getVert n = u ∧ n ≤ p.length := by
  constructor
  · intro h
    obtain ⟨q, r, hqr⟩ := SimpleGraph.Walk.mem_support_iff_exists_append.mp h
    use q.length
    rw [hqr]
    rw [Walk.getVert_append]
    simp only [lt_self_iff_false, ↓reduceIte, Nat.sub_self, getVert_zero, length_append,
      Nat.le_add_right, and_self]
  · rintro ⟨n, hn⟩
    rw [SimpleGraph.Walk.mem_support_iff]
    by_cases h0 : n = 0
    · rw [h0, getVert_zero] at hn
      left
      exact hn.1.symm
    · right
      have hnp : ¬ p.Nil := by
        rw [@nil_iff_length_eq]
        have : 1 ≤ p.length := by omega
        exact Nat.not_eq_zero_of_lt this
      rw [← support_tail_of_not_nil _ hnp]
      rw [mem_support_iff_exists_getVert]
      use n - 1
      simp only [Nat.sub_le_iff_le_add]
      rw [getVert_tail _ hnp, length_tail_add_one hnp]
      have : (n - 1 + 1) = n:= by omega
      rwa [this]
termination_by p.length
decreasing_by
· simp_wf
  rw [@Nat.lt_iff_add_one_le]
  rw [length_tail_add_one hnp]

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
    simp only [Walk.map_cons, edges_cons, List.map_cons, Sym2.map_pair_eq, List.cons.injEq,
      true_and, ih]

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

/-- The specialization of `SimpleGraph.Walk.map` for mapping walks to supergraphs. -/
abbrev mapLe {G G' : SimpleGraph V} (h : G ≤ G') {u v : V} (p : G.Walk u v) : G'.Walk u v :=
  p.map (Hom.mapSpanningSubgraphs h)

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

theorem transfer_eq_map_of_le (hp) (GH : G ≤ H) :
    p.transfer H hp = p.map (SimpleGraph.Hom.mapSpanningSubgraphs GH) := by
  induction p <;> simp [*]

@[simp]
theorem edges_transfer (hp) : (p.transfer H hp).edges = p.edges := by
  induction p <;> simp [*]

@[simp]
theorem support_transfer (hp) : (p.transfer H hp).support = p.support := by
  induction p <;> simp [*]

@[simp]
theorem length_transfer (hp) : (p.transfer H hp).length = p.length := by
  induction p <;> simp [*]

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

@[simp]
theorem transfer_append {w : V} (q : G.Walk v w) (hpq) :
    (p.append q).transfer H hpq =
      (p.transfer H fun e he => hpq _ (by simp [he])).append
        (q.transfer H fun e he => hpq _ (by simp [he])) := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp only [Walk.transfer, cons_append, cons.injEq, heq_eq_eq, true_and, ih]

@[simp]
theorem reverse_transfer (hp) :
    (p.transfer H hp).reverse =
      p.reverse.transfer H (by simp only [edges_reverse, List.mem_reverse]; exact hp) := by
  induction p with
  | nil => simp
  | cons _ _ ih => simp only [transfer_append, Walk.transfer, reverse_nil, reverse_cons, ih]

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
  p.toDeleteEdges {e} (fun e' => by contrapose!; simp (config := { contextual := true }) [hp])

@[simp]
theorem map_toDeleteEdges_eq (s : Set (Sym2 V)) {p : G.Walk v w} (hp) :
    Walk.map (Hom.mapSpanningSubgraphs (G.deleteEdges_le s)) (p.toDeleteEdges s hp) = p := by
  rw [← transfer_eq_map_of_le, transfer_transfer, transfer_self]
  intros e
  rw [edges_transfer]
  apply edges_subset_edgeSet p

end Walk

end SimpleGraph

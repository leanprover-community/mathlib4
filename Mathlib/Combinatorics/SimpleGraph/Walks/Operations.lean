/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Pim Otte, Daniel Weber, Rida Hamadani
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walks.Traversal

/-!
# Operations on walks

Operations on walks that produce a new walk in the same graph.

## Main definitions

* `SimpleGraph.Walk.copy`: Change the endpoints of a walk using equalities
* `SimpleGraph.Walk.append`: Concatenate two compatible walks
* `SimpleGraph.Walk.concat`: Concatenate an edge to the end of a walk
* `SimpleGraph.Walk.reverse`: Reverse a walk
* `SimpleGraph.Walk.drop`: Remove the first `n` darts of a walk
* `SimpleGraph.Walk.take`: Take the first `n` darts of a walk
* `SimpleGraph.Walk.tail`: Remove the first dart of a walk
* `SimpleGraph.Walk.dropLast`: Remove the last dart of a walk

## Tags
walks
-/

@[expose] public section

open Function

namespace SimpleGraph

namespace Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

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
theorem copy_nil {u u'} (hu : u = u') : (Walk.nil : G.Walk u u).copy hu hu = nil := by
  subst_vars
  rfl

theorem copy_cons {u v w u' w'} (h : G.Adj u v) (p : G.Walk v w) (hu : u = u') (hw : w = w') :
    (Walk.cons h p).copy hu hw = Walk.cons (hu ▸ h) (p.copy rfl hw) := by
  subst_vars
  rfl

@[simp]
theorem cons_copy {u v w v' w'} (h : G.Adj u v) (p : G.Walk v' w') (hv : v' = v) (hw : w' = w) :
    cons h (p.copy hv hw) = (Walk.cons (hv ▸ h) p).copy rfl hw := by
  subst_vars
  rfl

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
  induction p <;> simp [*]

theorem append_assoc {u v w x : V} (p : G.Walk u v) (q : G.Walk v w) (r : G.Walk w x) :
    p.append (q.append r) = (p.append q).append r := by
  induction p <;> simp [*]

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
    exact ⟨y, cons h q, h'', hc ▸ concat_cons _ _ _ ▸ rfl⟩

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
  ⟨reverse_injective, reverse_surjective⟩

@[simp]
theorem length_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).length = p.length := by
  subst_vars
  rfl

@[simp]
theorem length_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).length = p.length + q.length := by
  induction p <;> simp [*, add_comm, add_assoc]

@[simp]
theorem length_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).length = p.length + 1 := length_append _ _

@[simp]
protected theorem length_reverseAux {u v w : V} (p : G.Walk u v) (q : G.Walk u w) :
    (p.reverseAux q).length = p.length + q.length := by
  induction p with
  | nil => simp!
  | cons _ _ ih => simp [ih, Nat.succ_add, add_assoc]

@[simp]
theorem length_reverse {u v : V} (p : G.Walk u v) : p.reverse.length = p.length := by simp [reverse]

theorem getVert_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) (i : ℕ) :
    (p.append q).getVert i = if i < p.length then p.getVert i else q.getVert (i - p.length) := by
  induction p generalizing i <;> cases i <;> simp [*]

theorem getVert_reverse {u v : V} (p : G.Walk u v) (i : ℕ) :
    p.reverse.getVert i = p.getVert (p.length - i) := by
  induction p with
  | nil => rfl
  | cons h p ih =>
    simp only [reverse_cons, getVert_append, length_reverse, ih, length_cons]
    split_ifs
    next hi => simp [Nat.succ_sub hi.le]
    next hi =>
      obtain rfl | hi' := eq_or_gt_of_not_lt hi
      · simp
      · rw [Nat.eq_add_of_sub_eq (Nat.sub_pos_of_lt hi') rfl, Nat.sub_eq_zero_of_le hi']
        simp

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
  apply eq_of_heq (rec_heq_of_heq _ _)
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
    · simp only [concat_nil, concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he).symm).elim
  | cons _ _ ih =>
    rw [concat_cons] at he
    cases p'
    · simp only [concat_nil, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      exact (concat_ne_nil _ _ (heq_iff_eq.mp he)).elim
    · rw [concat_cons, cons.injEq] at he
      obtain ⟨rfl, he⟩ := he
      obtain ⟨rfl, rfl⟩ := ih (heq_iff_eq.mp he)
      exact ⟨rfl, rfl⟩

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

theorem support_append_eq_support_dropLast_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support = p.support.dropLast ++ p'.support := by
  induction p <;> simp_all [List.dropLast_cons_of_ne_nil]

theorem tail_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    (p.append p').support.tail = p.support.tail ++ p'.support.tail := by
  rw [support_append, List.tail_append_of_ne_nil (support_ne_nil _)]

theorem support_eq_concat {u v : V} (p : G.Walk u v) : p.support = p.support.dropLast.concat v := by
  cases p with
  | nil => rfl
  | cons h p =>
    obtain ⟨_, _, _, hq⟩ := exists_cons_eq_concat h p
    simp [hq]

@[simp]
theorem mem_tail_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support.tail ↔ t ∈ p.support.tail ∨ t ∈ p'.support.tail := by
  rw [tail_support_append, List.mem_append]

@[simp, nolint unusedHavesSuffices]
theorem mem_support_append_iff {t u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    t ∈ (p.append p').support ↔ t ∈ p.support ∨ t ∈ p'.support := by
  simp only [mem_support_iff, mem_tail_support_append_iff]
  obtain rfl | h := eq_or_ne t v <;> obtain rfl | h' := eq_or_ne t u <;>
    -- this `have` triggers the unusedHavesSuffices linter:
    (try have := h'.symm) <;> simp [*]

theorem support_subset_support_concat {u v w : V} (p : G.Walk u v) (hadj : G.Adj v w) :
    p.support ⊆ (p.concat hadj).support := by
  simp

@[simp]
theorem subset_support_append_left {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : p.support ⊆ (p.append q).support := by
  simp [support_append]

@[simp]
theorem subset_support_append_right {V : Type u} {G : SimpleGraph V} {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) : q.support ⊆ (p.append q).support := by
  intro
  simp +contextual [mem_support_append_iff]

theorem coe_support_append {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = {u} + p.support.tail + p'.support.tail := by
  rw [support_append, ← Multiset.coe_add, coe_support]

theorem coe_support_append' [DecidableEq V] {u v w : V} (p : G.Walk u v) (p' : G.Walk v w) :
    ((p.append p').support : Multiset V) = p.support + p'.support - {v} := by
  simp_rw [support_append, ← Multiset.coe_add, coe_support, add_comm ({v} : Multiset V),
    ← add_assoc, add_tsub_cancel_right]

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
  simp [edges]

theorem dart_snd_mem_support_of_mem_darts {u v : V} (p : G.Walk u v) {d : G.Dart}
    (h : d ∈ p.darts) : d.snd ∈ p.support := by
  simpa using p.reverse.dart_fst_mem_support_of_mem_darts (by simp [h] : d.symm ∈ p.reverse.darts)

theorem fst_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    t ∈ p.support := by
  obtain ⟨d, hd, he⟩ := List.mem_map.mp he
  rw [dart_edge_eq_mk'_iff'] at he
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact dart_fst_mem_support_of_mem_darts _ hd
  · exact dart_snd_mem_support_of_mem_darts _ hd

theorem snd_mem_support_of_mem_edges {t u v w : V} (p : G.Walk v w) (he : s(t, u) ∈ p.edges) :
    u ∈ p.support :=
  p.fst_mem_support_of_mem_edges (Sym2.eq_swap ▸ he)

theorem mem_support_of_mem_edges {u v w : V} {e : Sym2 V} {p : G.Walk u v} (he : e ∈ p.edges)
    (hv : w ∈ e) : w ∈ p.support :=
  hv.elim fun _ heq ↦ p.fst_mem_support_of_mem_edges <| heq ▸ he

theorem edges_nodup_of_support_nodup {u v : V} {p : G.Walk u v} (h : p.support.Nodup) :
    p.edges.Nodup := by
  induction p with
  | nil => simp
  | cons _ p' ih =>
    simp only [support_cons, List.nodup_cons, edges_cons] at h ⊢
    exact ⟨(h.1 <| fst_mem_support_of_mem_edges p' ·), ih h.2⟩

theorem nodup_tail_support_reverse {u : V} {p : G.Walk u u} :
    p.reverse.support.tail.Nodup ↔ p.support.tail.Nodup := by
  refine p.support_reverse ▸ p.support.nodup_tail_reverse ?_
  rw [← getVert_eq_support_getElem? _ (by cutsat), List.getLast?_eq_getElem?,
    ← getVert_eq_support_getElem? _ (by rw [Walk.length_support]; cutsat)]
  simp

@[simp]
lemma edgeSet_reverse {u v : V} (p : G.Walk u v) : p.reverse.edgeSet = p.edgeSet := by ext; simp

@[simp]
theorem edgeSet_concat {u v w : V} (p : G.Walk u v) (h : G.Adj v w) :
    (p.concat h).edgeSet = insert s(v, w) p.edgeSet := by ext; simp [or_comm]

theorem edgeSet_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    (p.append q).edgeSet = p.edgeSet ∪ q.edgeSet := by ext; simp

@[simp]
theorem edgeSet_copy {u v u' v'} (p : G.Walk u v) (hu : u = u') (hv : v = v') :
    (p.copy hu hv).edgeSet = p.edgeSet := by ext; simp

@[simp]
lemma nil_append_iff {p : G.Walk u v} {q : G.Walk v w} : (p.append q).Nil ↔ p.Nil ∧ q.Nil := by
  cases p <;> cases q <;> simp

lemma Nil.append {p : G.Walk u v} {q : G.Walk v w} (hp : p.Nil) (hq : q.Nil) : (p.append q).Nil :=
  by simp [hp, hq]

@[simp]
lemma nil_reverse {p : G.Walk v w} : p.reverse.Nil ↔ p.Nil := by
  cases p <;> simp

/-- The walk obtained by removing the first `n` darts of a walk. -/
def drop {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk (p.getVert n) v :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => p.copy (getVert_zero p).symm rfl
  | .cons _ q, (n + 1) => q.drop n

@[simp]
lemma drop_length (p : G.Walk u v) (n : ℕ) : (p.drop n).length = p.length - n := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

@[simp]
lemma drop_getVert (p : G.Walk u v) (n m : ℕ) : (p.drop n).getVert m = p.getVert (n + m) := by
  induction p generalizing n <;> cases n <;> simp [*, drop, add_right_comm]

/-- The walk obtained by taking the first `n` darts of a walk. -/
def take {u v : V} (p : G.Walk u v) (n : ℕ) : G.Walk u (p.getVert n) :=
  match p, n with
  | .nil, _ => .nil
  | p, 0 => nil.copy rfl (getVert_zero p).symm
  | .cons h q, (n + 1) => .cons h (q.take n)

@[simp]
lemma take_length (p : G.Walk u v) (n : ℕ) : (p.take n).length = n ⊓ p.length := by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[simp]
lemma take_getVert (p : G.Walk u v) (n m : ℕ) : (p.take n).getVert m = p.getVert (n ⊓ m) := by
  induction p generalizing n m <;> cases n <;> cases m <;> simp [*, take]

lemma take_support_eq_support_take_succ {u v} (p : G.Walk u v) (n : ℕ) :
    (p.take n).support = p.support.take (n + 1) := by
  induction p generalizing n <;> cases n <;> simp [*, take]

@[simp]
lemma penultimate_concat {t u v} (p : G.Walk u v) (h : G.Adj v t) :
    (p.concat h).penultimate = v := by simp [concat_eq_append, getVert_append]

@[simp]
lemma snd_reverse (p : G.Walk u v) : p.reverse.snd = p.penultimate := by
  simpa using getVert_reverse p 1

@[simp]
lemma penultimate_reverse (p : G.Walk u v) : p.reverse.penultimate = p.snd := by
  cases p <;> simp [snd, getVert_append]

/-- The walk obtained by removing the first dart of a walk. A nil walk stays nil. -/
def tail (p : G.Walk u v) : G.Walk (p.snd) v := p.drop 1

lemma drop_zero {u v} (p : G.Walk u v) :
    p.drop 0 = p.copy (getVert_zero p).symm rfl := by
  cases p <;> simp [Walk.drop]

lemma drop_support_eq_support_drop_min {u v} (p : G.Walk u v) (n : ℕ) :
    (p.drop n).support = p.support.drop (n ⊓ p.length) := by
  induction p generalizing n <;> cases n <;> simp [*, drop]

/-- The walk obtained by removing the last dart of a walk. A nil walk stays nil. -/
def dropLast (p : G.Walk u v) : G.Walk u p.penultimate := p.take (p.length - 1)

@[simp]
lemma tail_nil : (@nil _ G v).tail = .nil := rfl

@[simp]
lemma tail_cons_nil (h : G.Adj u v) : (Walk.cons h .nil).tail = .nil := rfl

@[simp]
lemma tail_cons (h : G.Adj u v) (p : G.Walk v w) :
    (p.cons h).tail = p.copy (getVert_zero p).symm rfl := by
  cases p <;> rfl

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
    rw [dropLast_cons_of_not_nil] <;> simp [*, nil_iff_length_eq]

lemma cons_tail_eq (p : G.Walk u v) (hp : ¬ p.Nil) :
    cons (p.adj_snd hp) p.tail = p := by
  cases p <;> simp at hp ⊢

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

protected lemma Nil.tail {p : G.Walk v w} (hp : p.Nil) : p.tail.Nil := by
  cases p <;> simp [not_nil_cons] at hp ⊢

lemma not_nil_of_tail_not_nil {p : G.Walk v w} (hp : ¬ p.tail.Nil) : ¬ p.Nil := mt Nil.tail hp

@[simp] lemma nil_copy {u' v' : V} {p : G.Walk u v} (hu : u = u') (hv : v = v') :
    (p.copy hu hv).Nil = p.Nil := by
  subst_vars
  rfl

lemma support_tail_of_not_nil (p : G.Walk u v) (hp : ¬ p.Nil) :
    p.tail.support = p.support.tail := by
  rw [← cons_support_tail p hp, List.tail_cons]

@[deprecated (since := "2025-08-26")] alias support_tail := support_tail_of_not_nil

@[simp] lemma getVert_copy {u v w x : V} (p : G.Walk u v) (i : ℕ) (h : u = w) (h' : v = x) :
    (p.copy h h').getVert i = p.getVert i := by
  subst_vars
  rfl

@[simp] lemma getVert_tail {u v n} (p : G.Walk u v) :
    p.tail.getVert n = p.getVert (n + 1) := by
  cases p <;> simp

lemma getVert_mem_tail_support {u v : V} {p : G.Walk u v} (hp : ¬p.Nil) :
    ∀ {i : ℕ}, i ≠ 0 → p.getVert i ∈ p.support.tail
  | i + 1, _ => by
    rw [← getVert_tail, ← p.support_tail_of_not_nil hp]
    exact getVert_mem_support ..

lemma ext_support {u v} {p q : G.Walk u v} (h : p.support = q.support) :
    p = q := by
  induction q with
  | nil => exact nil_iff_eq_nil.mp (nil_iff_support_eq.mpr (support_nil ▸ h))
  | cons ha q ih =>
    cases p with
    | nil => simp at h
    | cons _ p =>
      simp only [support_cons, List.cons.injEq, true_and] at h
      apply List.getElem_of_eq at h
      specialize h (i := 0) (by simp)
      simp_rw [List.getElem_zero, p.head_support, q.head_support] at h
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
  · exact (this (h · |>.symm) (le_of_not_ge hpq)).symm
  refine ext_getVert_le_length (hpq.antisymm ?_) fun k _ ↦ h k
  by_contra!
  exact (q.adj_getVert_succ this).ne (by simp [← h, getVert_of_length_le])

end Walk

end SimpleGraph

/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Daniel Weber
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walks.Basic

/-!
# Traversing walks

Functions that help access different parts of a walk.

## Main definitions

* `SimpleGraph.Walk.getVert`:
  Get the nth vertex encountered in a walk, or the last one if `n` is too large
* `SimpleGraph.Walk.snd`: The second vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.penultimate`:
  The penultimate vertex of a walk, or the only vertex in an empty walk
* `SimpleGraph.Walk.firstDart`: The first dart of a non-empty walk
* `SimpleGraph.Walk.lastDart`: The last dart of a non-empty walk

## Tags
walks
-/

@[expose] public section

namespace SimpleGraph

namespace Walk

universe u
variable {V : Type u} {G : SimpleGraph V} {u v w : V}

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
theorem getVert_mem_support {u v : V} (p : G.Walk u v) (i : ℕ) : p.getVert i ∈ p.support := by
  induction p generalizing i <;> cases i <;> simp [*]

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

theorem darts_getElem_eq_getVert {u v : V} {p : G.Walk u v} (n : ℕ) (h : n < p.darts.length) :
    p.darts[n] = ⟨⟨p.getVert n, p.getVert (n + 1)⟩, p.adj_getVert_succ (p.length_darts ▸ h)⟩ := by
  rw [p.length_darts] at h
  ext
  · simp only [p.getVert_eq_support_getElem (le_of_lt h)]
    by_cases h' : n = 0
    · simp [h', List.getElem_zero]
    · have := p.isChain_dartAdj_darts.getElem (n - 1) (by grind)
      grind [DartAdj, =_ cons_map_snd_darts]
  · simp [p.getVert_eq_support_getElem h, ← p.cons_map_snd_darts]

/-- The second vertex of a walk, or the only vertex in a nil walk. -/
abbrev snd (p : G.Walk u v) : V := p.getVert 1

@[simp] lemma adj_snd {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj v p.snd := by
  simpa using adj_getVert_succ p (by simpa [not_nil_iff_lt_length] using hp : 0 < p.length)

lemma snd_cons {u v w} (q : G.Walk v w) (hadj : G.Adj u v) :
    (q.cons hadj).snd = v := by simp

lemma snd_mem_tail_support {u v : V} {p : G.Walk u v} (h : ¬p.Nil) : p.snd ∈ p.support.tail :=
  p.notNilRec (by simp) h

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
lemma adj_penultimate {p : G.Walk v w} (hp : ¬ p.Nil) :
    G.Adj p.penultimate w := by
  conv => rhs; rw [← getVert_length p]
  rw [nil_iff_length_eq] at hp
  convert adj_getVert_succ _ _ <;> omega

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

theorem firstDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) :
    p.firstDart h₁ = p.darts[0] := by
  simp [Dart.ext_iff, firstDart_toProd, darts_getElem_eq_getVert]

theorem lastDart_eq {p : G.Walk v w} (h₁ : ¬ p.Nil) (h₂ : 0 < p.darts.length) :
    p.lastDart h₁ = p.darts[p.darts.length - 1] := by
  simp (disch := grind) [Dart.ext_iff, lastDart_toProd, darts_getElem_eq_getVert,
    p.getVert_of_length_le]

end Walk

end SimpleGraph

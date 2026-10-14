/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Cayley
public import Mathlib.Combinatorics.SimpleGraph.Metric
public import Mathlib.Geometry.Group.WordMetric

/-!
# The Cayley graph of a generating family

We define the Cayley graph of a group `G` with respect to a generating family
`P : Group.Generators G ι` and relate it to words over `P`:
a word `l` gives a walk from `g` to `g * P.wordProd l` of length at most `l.length`,
and a walk from `g` to `h` gives a word of the same length which evaluates to `g⁻¹ * h`.
We use this to show that the graph distance in the Cayley graph is given by the word length.

## Main definitions

* `Group.Generators.cayleySimpleGraph`: the Cayley graph of `G` with respect to a generating
  family `P`, realized as a `SimpleGraph G`.

## Main results

* `Group.Generators.cayleySimpleGraph_connected`: the Cayley graph is connected.
* `Group.Generators.dist_cayleySimpleGraph`: the distance from `g` to `h` in the Cayley graph is
  the word length of `g⁻¹ * h`.

## Implementation notes

* `SimpleGraph.mulCayley` is used to construct the Cayley graph induced by elements of `G`.
* A simple graph has no loops, so a letter that evaluates to `1` in the group contributes no edge.
  This is why `exists_walk_of_word` produces a walk which may be shorter than the word.

## Tags

Cayley graph, word metric, word length, geometric group theory
-/

@[expose] public section

open SimpleGraph

namespace Group.Generators

variable {G ι : Type*} [Group G]

variable (P : Group.Generators G ι) (g h : G) (l : List (ι × Bool))

/-- The Cayley graph of `G` with respect to the generating family `P`. -/
def cayleySimpleGraph : SimpleGraph G := mulCayley (Set.range P.val)

/-- `g` is a letter of `P` if it is the value of a one-letter word. -/
def IsLetter : Prop := ∃ x : ι × Bool, P.wordProd [x] = g

/-- `g` is a letter of `P` if and only if it is a generator or the inverse of one. -/
lemma isLetter_iff : P.IsLetter g ↔ g ∈ Set.range P.val ∨ g⁻¹ ∈ Set.range P.val := by
  constructor
  · intro hg
    obtain ⟨⟨i, b⟩, rfl⟩ := hg
    cases b <;> simp
  · intro hg
    obtain ⟨i, hi⟩ | ⟨i, hi⟩ := hg
    · use (i, true); simp [hi]
    · use (i, false); simp [hi]

/-- `g` and `h` are adjacent in the Cayley graph if and only if they are distinct and
`g⁻¹ * h` is a letter of `P`. -/
lemma cayleySimpleGraph_adj : P.cayleySimpleGraph.Adj g h ↔ g ≠ h ∧ P.IsLetter (g⁻¹ * h) := by
  simp [cayleySimpleGraph, mulCayley_adj, isLetter_iff]

/-! ### Words and walks -/

/-- A word `l` gives a walk in the Cayley graph from `g` to `g * P.wordProd l`,
of length at most the length of `l`. -/
lemma exists_walk_of_word (g : G) (l : List (ι × Bool)) :
    ∃ p : P.cayleySimpleGraph.Walk g (g * P.wordProd l), p.length ≤ l.length := by
  match l with
  | [] => simp
  | (i, b) :: tail =>
    let s := cond b (P.val i) (P.val i)⁻¹
    obtain ⟨p, hp⟩ := exists_walk_of_word (g * s) tail
    have hprod : g * s * (P.wordProd tail) = g * P.wordProd ((i, b) :: tail) := by
      rw [wordProd_cons, mul_assoc]
    obtain heq | hne := eq_or_ne g (g * s)
    -- we have to handle the case when `s = 1` because letter in a word may evaluate to `1`
    · use p.copy heq.symm hprod
      simp [hp.trans]
    · have hadj : P.cayleySimpleGraph.Adj g (g * s) := by
        rw [cayleySimpleGraph_adj]
        exact ⟨by assumption, by use (i, b); simp [s]⟩
      use (Walk.cons hadj p).copy rfl hprod
      simp [hp]

/-- A walk in the Cayley graph from `g` to `h` gives a word of the same length which evaluates to
`g⁻¹ * h`. -/
lemma exists_word_of_walk {g h : G} (p : P.cayleySimpleGraph.Walk g h) :
    ∃ l, P.wordProd l = g⁻¹ * h ∧ l.length = p.length := by
  match p with
  | .nil =>
    use []; simp
  | .cons (v := b) hadj q =>
    obtain ⟨l, hprod, hl⟩ := exists_word_of_walk q
    have hgen : P.IsLetter (g⁻¹ * b) := by
      rw [cayleySimpleGraph_adj] at hadj
      exact hadj.right
    obtain ⟨x, hx⟩ := hgen
    use [x] ++ l
    constructor
    · rw [wordProd_append, hx, hprod]; simp
    · simp [hl]

/-! ### Connectedness -/

/-- The Cayley graph is preconnected: any two vertices can be joined by a walk. -/
lemma cayleySimpleGraph_preconnected : P.cayleySimpleGraph.Preconnected := by
  intro g h
  obtain ⟨l, hl⟩ := P.wordProd_surjective (g⁻¹ * h)
  obtain ⟨p, -⟩ := P.exists_walk_of_word g l
  simp [hl] at p
  exact p.reachable

/-- The Cayley graph is connected: preconnected and nonempty. -/
theorem cayleySimpleGraph_connected : P.cayleySimpleGraph.Connected := by
  constructor; exact P.cayleySimpleGraph_preconnected

/-! ### Distance -/

/-- The distance from `g` to `h` in the Cayley graph is the word length of `g⁻¹ * h`. -/
theorem dist_cayleySimpleGraph : P.cayleySimpleGraph.dist g h = P.wordLength (g⁻¹ * h) := by
  apply le_antisymm
  · obtain ⟨l, hl, hprod⟩ := P.exists_isGeodesic (g⁻¹ * h)
    obtain ⟨p, hp⟩ := P.exists_walk_of_word g l
    rw [← hprod, hl.eq]
    have heq : h = g * P.wordProd l := by simp [hprod]
    subst heq
    exact (dist_le p).trans hp
  · have hconn := P.cayleySimpleGraph_preconnected g h
    obtain ⟨p, hp⟩ := hconn.exists_walk_length_eq_dist
    obtain ⟨l, hprod, hl⟩ := P.exists_word_of_walk p
    rw [← hp, ← hl, wordLength_le_iff]
    use l

/-- The word length of `g` is its distance from `1` in the Cayley graph. -/
@[simp]
lemma dist_cayleySimpleGraph_one_left : P.cayleySimpleGraph.dist 1 g = P.wordLength g := by
  simp [dist_cayleySimpleGraph]

end Group.Generators

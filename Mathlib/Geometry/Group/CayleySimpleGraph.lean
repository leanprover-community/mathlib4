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
* `AddGroup.Generators.cayleySimpleGraph`: the additive version of the above.
* `Group.Generators.walkWord`: the word read along a walk in the Cayley graph, one letter for
  each dart.

## Main results

* `Group.Generators.dist_cayleySimpleGraph`: the distance from `g` to `h` in the Cayley graph is
  the word length of `g⁻¹ * h`.
* `AddGroup.Generators.dist_cayleySimpleGraph`: the additive version of the above.

## Implementation notes

* `SimpleGraph.mulCayley` (resp. `SimpleGraph.addCayley`) is used to construct the Cayley graph
  induced by elements of `G`.
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
@[to_additive /-- The Cayley graph of `G` with respect to the generating family `P`. -/]
def cayleySimpleGraph : SimpleGraph G := mulCayley (Set.range P.val)

/-- `g` is a letter of `P` if it is the value of a one-letter word. -/
@[to_additive /-- `g` is a letter of `P` if it is the value of a one-letter word. -/]
def IsLetter : Prop := ∃ x : ι × Bool, P.wordProd [x] = g

variable {g} in
/-- `g` is a letter of `P` if and only if it is a generator or the inverse of one. -/
@[to_additive /-- `g` is a letter of `P` if and only if it is a generator or the negative of
one. -/]
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
@[to_additive /-- `g` and `h` are adjacent in the Cayley graph if and only if they are distinct
and `-g + h` is a letter of `P`. -/]
lemma cayleySimpleGraph_adj : P.cayleySimpleGraph.Adj g h ↔ g ≠ h ∧ P.IsLetter (g⁻¹ * h) := by
  simp [cayleySimpleGraph, mulCayley_adj, isLetter_iff]

/-! ### Words and walks -/

/-- A word `l` gives a walk in the Cayley graph from `g` to `g * P.wordProd l`,
of length at most the length of `l`. -/
@[to_additive /-- A word `l` gives a walk in the Cayley graph from `g` to `g + P.wordSum l`,
of length at most the length of `l`. -/]
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
@[to_additive /-- A walk in the Cayley graph from `g` to `h` gives a word of the same length which
evaluates to `-g + h`. -/]
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

/-! ### Distance -/

/-- The distance from `g` to `h` in the Cayley graph is the word length of `g⁻¹ * h`. -/
@[to_additive /-- The distance from `g` to `h` in the Cayley graph is the word length of
`-g + h`. -/]
theorem dist_cayleySimpleGraph : P.cayleySimpleGraph.dist g h = P.wordLength (g⁻¹ * h) := by
  -- get sufficiently short walk between `g` and `h`; gives reachability and the ≤ direction
  obtain ⟨p, hp⟩ : ∃ p : P.cayleySimpleGraph.Walk g h, p.length ≤ P.wordLength (g⁻¹ * h) := by
    obtain ⟨l, hl, hprod⟩ := P.exists_isGeodesic (g⁻¹ * h)
    rw [IsGeodesic, hprod] at hl
    obtain ⟨p, hp⟩ := P.exists_walk_of_word g l
    use p.copy rfl (by simp [hprod])
    rw [Walk.length_copy, hl]
    exact hp
  apply le_antisymm
  · calc P.cayleySimpleGraph.dist g h ≤ p.length := dist_le p
      _ ≤ P.wordLength (g⁻¹ * h) := hp
  · obtain ⟨q, hq⟩ := p.reachable.exists_walk_length_eq_dist
    obtain ⟨l, hl, hlen⟩ := P.exists_word_of_walk q
    rw [← hl]
    calc P.wordLength (P.wordProd l) ≤ l.length := P.wordLength_wordProd_le l
      _ = q.length := hlen
      _ = P.cayleySimpleGraph.dist g h := hq

/-- The word length of `g` is its distance from `1` in the Cayley graph. -/
@[to_additive (attr := simp)
/-- The word length of `g` is its distance from `0` in the Cayley graph. -/]
lemma dist_cayleySimpleGraph_one_left : P.cayleySimpleGraph.dist 1 g = P.wordLength g := by
  simp [dist_cayleySimpleGraph]

/-! ### The word read along a walk -/

/-- For a dart `d` of the Cayley graph, `d.fst⁻¹ * d.snd` is a letter of `P`. -/
@[to_additive /-- For a dart `d` of the Cayley graph, `-d.fst + d.snd` is a letter of `P`. -/]
lemma isLetter_dartFstInvMulSnd (d : P.cayleySimpleGraph.Dart) : P.IsLetter (d.fst⁻¹ * d.snd) :=
  ((P.cayleySimpleGraph_adj d.fst d.snd).mp d.adj).2

/-- A letter of `P` evaluating to `d.fst⁻¹ * d.snd`, for a dart `d` of the Cayley graph. -/
@[to_additive
/-- A letter of `P` evaluating to `-d.fst + d.snd`, for a dart `d` of the Cayley graph. -/]
noncomputable def dartLetter (d : P.cayleySimpleGraph.Dart) : ι × Bool :=
  (P.isLetter_dartFstInvMulSnd d).choose

/-- The word read along a walk in the Cayley graph: the letters of its darts, in order. -/
@[to_additive
/-- The word read along a walk in the Cayley graph: the letters of its darts, in order. -/]
noncomputable def walkWord {u v : G} (p : P.cayleySimpleGraph.Walk u v) : List (ι × Bool) :=
  p.darts.map P.dartLetter

/-- The letter of a dart `d` evaluates to `d.fst⁻¹ * d.snd`. -/
@[to_additive (attr := simp) /-- The letter of a dart `d` evaluates to `-d.fst + d.snd`. -/]
lemma wordProd_dartLetter (d : P.cayleySimpleGraph.Dart) :
    P.wordProd [P.dartLetter d] = d.fst⁻¹ * d.snd :=
  (P.isLetter_dartFstInvMulSnd d).choose_spec

end Group.Generators

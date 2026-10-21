/-
Copyright (c) 2026 Dmitry Kaysin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dmitry Kaysin
-/
module

public import Mathlib.Geometry.Group.CayleySimpleGraph

/-!
# Reduced words and non-backtracking walks in Cayley graphs

For a generating family `P : Group.Generators G ι`, a walk in the Cayley graph `P.cayleySimpleGraph`
reads a word. We show that, given a walk `p`, the word read along `p` is reduced if `p` is
non-backtracking. Conversely, if the letters of the generating family have pairwise distinct values
and the word read along `p` is reduced, then `p` is non-backtracking.

## Main results

* `Group.Generators.isReduced_walkWord_of_isNonBacktracking`: the word read along a
  non-backtracking walk is reduced.
* `Group.Generators.isNonBacktracking_of_isReduced_walkWord`: if letters of `P` have pairwise
  distinct values, then a walk along which the word read is reduced does not backtrack.

## Implementation notes

* Letters of `P` have pairwise distinct values, i.e. `fun x : ι × Bool ↦ P.wordProd [x]` is
  injective if and only if `P` is injective and no product of two generators is trivial.

## Tags

Cayley graph, non-backtracking walk, reduced word, geometric group theory
-/

@[expose] public section

open SimpleGraph

/-! ### Reduced words and non-backtracking walks -/

namespace Group.Generators

variable {G ι : Type*} [Group G] (P : Group.Generators G ι)

@[to_additive]
private lemma eq_symm_iff_wordProd_dartLetter_eq_inv {d d' : P.cayleySimpleGraph.Dart}
    (h : P.cayleySimpleGraph.DartAdj d d') :
    d = d'.symm ↔ P.wordProd [P.dartLetter d'] = (P.wordProd [P.dartLetter d])⁻¹ := by
  rw [wordProd_dartLetter, wordProd_dartLetter, mul_inv_rev, inv_inv, ← h, mul_left_cancel_iff,
    Dart.ext_iff, Prod.ext_iff]
  exact (and_iff_left h).trans eq_comm

/-- The word read along a non-backtracking walk is reduced. -/
@[to_additive /-- The word read along a non-backtracking walk is reduced. -/]
lemma isReduced_walkWord_of_isNonBacktracking {u v : G} (p : P.cayleySimpleGraph.Walk u v)
    (hnb : p.IsNonBacktracking) : FreeGroup.IsReduced (P.walkWord p) := by
  rw [Walk.isNonBacktracking_def] at hnb
  rw [FreeGroup.IsReduced, walkWord, List.isChain_map]
  refine p.isChain_dartAdj_darts.imp_of_isChain ?_ hnb
  intro d d' h hne h1
  -- if the letters of `d` and `d'` cancel, then `d` is the reverse of `d'`
  by_contra h2
  apply hne
  have hinv : P.dartLetter d' = ((P.dartLetter d).1, !(P.dartLetter d).2) :=
    Prod.ext h1.symm (Bool.eq_not_iff.mpr (Ne.symm h2))
  rw [P.eq_symm_iff_wordProd_dartLetter_eq_inv h, hinv]
  exact P.wordProd_invRev [P.dartLetter d]

/-- If letters of `P` have pairwise distinct values, then a walk along which the word read is
reduced does not backtrack. -/
@[to_additive /-- If letters of `P` have pairwise distinct values, then a walk along which the word
read is reduced does not backtrack. -/]
lemma isNonBacktracking_of_isReduced_walkWord {u v : G} (p : P.cayleySimpleGraph.Walk u v)
    (hP : Function.Injective fun x : ι × Bool ↦ P.wordProd [x])
    (hred : FreeGroup.IsReduced (P.walkWord p)) : p.IsNonBacktracking := by
  rw [FreeGroup.IsReduced, walkWord, List.isChain_map] at hred
  rw [Walk.isNonBacktracking_def]
  refine p.isChain_dartAdj_darts.imp_of_isChain ?_ hred
  intro d d' h hcancel heq
  -- if `d` is the reverse of `d'`, then their letters cancel
  rw [P.eq_symm_iff_wordProd_dartLetter_eq_inv h, ← P.wordProd_invRev] at heq
  have hinv : P.dartLetter d' = ((P.dartLetter d).1, !(P.dartLetter d).2) := hP heq
  rw [hinv] at hcancel
  simp at hcancel

end Group.Generators

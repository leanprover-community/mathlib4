/-
Copyright (c) 2026 Zixiao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zixiao Wang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic

/-!
# The global, local, and pairwise Markov properties

An independence relation is a ternary relation on sets. A semigraphoid satisfies symmetry,
decomposition, weak union, and contraction. This module connects such relations to separation
in an undirected graph.

## Main definitions and results

* `IndependenceRelation` and `IndependenceRelation.IsSemigraphoid`: abstract independence.
* `SimpleGraph.Separates`: every walk between the two sets meets the separating set.
* `IndependenceRelation.IsGlobalMarkov`, `IndependenceRelation.IsLocalMarkov`, and
  `IndependenceRelation.IsPairwiseMarkov`: the three graphical Markov properties.
* `IndependenceRelation.IsGlobalMarkov.isLocalMarkov`: global implies local, with no axioms
  on the independence relation.
* `IndependenceRelation.IsLocalMarkov.isPairwiseMarkov`: local implies pairwise for a semigraphoid.

## Implementation notes

The vertex type is arbitrary. Semigraphoid axioms apply to all subsets, including overlapping
sets. Global Markov requires pairwise disjoint sets and allows empty sets. The conditioning
set in local Markov is the entire neighborhood, which may be infinite.

## References

* [David Montague and Bala Rajaratnam,
  *Graphical Markov models for infinitely many variables*][MontagueRajaratnam2018]

## Tags

conditional independence, semigraphoid, graphical model, Markov property, graph separation
-/

@[expose] public section

open Set

universe u

/-- An abstract independence relation on subsets of a type.
`R A B S` expresses that `A` and `B` are independent given `S`. -/
abbrev IndependenceRelation (V : Type*) := Set V → Set V → Set V → Prop

namespace IndependenceRelation

variable {V : Type u}

/-- An independence relation satisfying symmetry, decomposition, weak union, and contraction.
The axioms apply to arbitrary subsets, including infinite and overlapping sets. -/
structure IsSemigraphoid (R : IndependenceRelation V) : Prop where
  /-- Symmetry in the two independent sets. -/
  symm : ∀ {A B S}, R A B S → R B A S
  /-- Independence from a union implies independence from each set. -/
  decomp : ∀ {A B C S}, R A (B ∪ C) S → R A B S ∧ R A C S
  /-- Part of the second set can be moved into the conditioning set. -/
  weak_union : ∀ {A B C S}, R A (B ∪ C) S → R A B (S ∪ C)
  /-- Combine independence statements with nested conditioning sets. -/
  contraction : ∀ {A B C S}, R A B (S ∪ C) → R A C S → R A (B ∪ C) S

end IndependenceRelation

namespace SimpleGraph

variable {V : Type*}

/-- `G.Separates A B S` means that every walk in `G` from `A` to `B` contains a vertex of `S`,
possibly at an endpoint. -/
def Separates (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ S

/-- The neighborhood of a vertex separates it from the vertices outside its closed neighborhood. -/
theorem neighborSet_separates_singleton (G : SimpleGraph V) (i : V) :
    G.Separates {i} (({i} ∪ G.neighborSet i)ᶜ) (G.neighborSet i) := by
  rintro a b rfl hb p
  cases p with
  | nil => exact (hb (Or.inl rfl)).elim
  | cons hij q => exact ⟨_, by simp, hij⟩

end SimpleGraph

namespace IndependenceRelation

open SimpleGraph

variable {V : Type u}

/-- Any two distinct nonadjacent vertices are independent given all remaining vertices. -/
def IsPairwiseMarkov (R : IndependenceRelation V) (G : SimpleGraph V) : Prop :=
  ∀ ⦃i j : V⦄, i ≠ j → ¬ G.Adj i j → R {i} {j} ({i, j}ᶜ)

/-- Each vertex is independent of the vertices outside its closed neighborhood,
given its neighborhood. -/
def IsLocalMarkov (R : IndependenceRelation V) (G : SimpleGraph V) : Prop :=
  ∀ i, R {i} (({i} ∪ G.neighborSet i)ᶜ) (G.neighborSet i)

/-- For pairwise disjoint sets `A`, `B`, and `S`, separation of `A` and `B` by `S`
implies their independence given `S`. -/
def IsGlobalMarkov (R : IndependenceRelation V) (G : SimpleGraph V) : Prop :=
  ∀ ⦃A B S : Set V⦄, Disjoint A B → Disjoint A S → Disjoint B S →
    G.Separates A B S → R A B S

/-- The global Markov property implies the local Markov property for any independence relation. -/
theorem IsGlobalMarkov.isLocalMarkov {R : IndependenceRelation V} {G : SimpleGraph V}
    (h : IsGlobalMarkov R G) : IsLocalMarkov R G := fun i ↦
  h (by simp) (by simp) (by simp [disjoint_compl_left_iff])
    (G.neighborSet_separates_singleton i)

/-- The local Markov property implies the pairwise Markov property for a semigraphoid. -/
theorem IsLocalMarkov.isPairwiseMarkov {R : IndependenceRelation V} {G : SimpleGraph V}
    (hR : IsSemigraphoid R) (h : IsLocalMarkov R G) : IsPairwiseMarkov R G := by
  intro i j hij hadj
  convert hR.weak_union (B := {j}) (C := (({i} ∪ G.neighborSet i)ᶜ \ {j}))
    (by simpa [hij.symm, hadj] using h i) using 1
  apply compl_injective
  simp [compl_sdiff, inter_insert_of_mem, hadj]

end IndependenceRelation

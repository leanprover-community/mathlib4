/-
Copyright (c) 2026 Zixiao Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zixiao Wang
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Walk.Decomp
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# The global, local, and pairwise Markov properties

An independence relation is a ternary relation on sets. Semigraphoids use symmetry and
the chain rule on arbitrary subsets. `IsGraphoid` adds general intersection (P5*) from
Montague and Rajaratnam: for any partition of `X` into finite blocks, independence of
each block from `Y` given `S` and all other blocks implies independence of `X` from `Y`
given `S`. The family of blocks may be infinite.

## Main definitions and results

* `IsGraphoid`: a semigraphoid with `HasGeneralIntersection`.
* `IsOrdinaryGraphoid`: the weaker binary-intersection variant for comparison.
* `partition_other_blocks_eq_sdiff`: identifies the union of the other partition blocks
  with `X \ B`, as used in the formal axiom.
* `IsGraphoid.indep_of_singletons`: combines arbitrarily many singleton statements.
* `IsGraphoid.hasEmptyIndependence`: follows from the empty partition.
* `SimpleGraph.Separates`: every walk between two sets meets the separating set.
* `IsPairwiseMarkov`, `IsLocalMarkov`, and `IsGlobalMarkov`: graphical Markov properties.
* `IsGlobalMarkov.isLocalMarkov`: global implies local without relational axioms.
* `IsLocalMarkov.isPairwiseMarkov`: local implies pairwise for a semigraphoid.
* `IsPairwiseMarkov.isGlobalMarkov`: pairwise implies global for a (P5*) graphoid.

## Implementation notes

`R : Set V → Set V → Set V → Prop` represents independence of the first two sets given
the third. The vertex type, neighborhoods, and subsets need not be finite or countable.
Global Markov is restricted to pairwise disjoint triples; semigraphoid axioms and general
intersection apply to all subsets. A partition is represented by a pairwise disjoint set
of blocks whose union is `X`. Each block is finite; the family of blocks is unrestricted.
The empty partition is permitted when `X = ∅`, so (P5*) supplies empty-set independence.

These are abstract relational axioms, without probabilistic positivity assumptions.

## References

* [David Montague and Bala Rajaratnam,
  *Graphical Markov models for infinitely many variables*][MontagueRajaratnam2018]

## Tags

conditional independence, semigraphoid, graphical model, Markov property, graph separation
-/

@[expose] public section

open Set

universe u

namespace IndependenceRelation

variable {V : Type u}

/-- Symmetry and the chain rule, in the form used in Proposition 9.1.2.
Unlike the book's disjoint-set convention, these axioms apply to all subsets, including
infinite and overlapping sets. -/
structure IsSemigraphoid (R : Set V → Set V → Set V → Prop) : Prop where
  /-- Symmetry in the two independent sets. -/
  symm : ∀ {A B S}, R A B S → R B A S
  /-- The chain rule combines decomposition, weak union, and contraction. -/
  chain_rule : ∀ {A B C S}, R A B (S ∪ C) ∧ R A C S ↔ R A (B ∪ C) S

namespace IsSemigraphoid

variable {R : Set V → Set V → Set V → Prop} (h : IsSemigraphoid R)
include h

/-- Symmetry as an equivalence, in the form stated in Proposition 9.1.2. -/
theorem symm_iff {A B S : Set V} : R A B S ↔ R B A S :=
  ⟨h.symm, h.symm⟩

/-- Independence from a union implies independence from each set. -/
theorem decomp {A B C S : Set V} (hR : R A (B ∪ C) S) : R A B S ∧ R A C S :=
  ⟨(h.chain_rule.mpr (union_comm B C ▸ hR)).2, (h.chain_rule.mpr hR).2⟩

/-- Part of the second set can be moved into the conditioning set. -/
theorem weak_union {A B C S : Set V} (hR : R A (B ∪ C) S) : R A B (S ∪ C) :=
  (h.chain_rule.mpr hR).1

/-- Combine independence statements with nested conditioning sets. -/
theorem contraction {A B C S : Set V} (hB : R A B (S ∪ C)) (hC : R A C S) :
    R A (B ∪ C) S :=
  h.chain_rule.mp ⟨hB, hC⟩

/-- Independence is preserved when restricting the second set. -/
theorem mono_right {A B B' S : Set V} (hR : R A B S) (hB : B' ⊆ B) : R A B' S :=
  (h.decomp (B := B') (C := B) ((union_eq_self_of_subset_left hB).symm ▸ hR)).1

/-- Independence is preserved when restricting the first set. -/
theorem mono_left {A A' B S : Set V} (hR : R A B S) (hA : A' ⊆ A) : R A' B S :=
  h.symm (h.mono_right (h.symm hR) hA)

end IsSemigraphoid


/-- Independence from the empty set, separately assumed when needed.
This is not one of the graphoid axioms in Proposition 9.1.2. -/
def HasEmptyIndependence (R : Set V → Set V → Set V → Prop) : Prop :=
  ∀ ⦃A S : Set V⦄, Disjoint A S → R A ∅ S

/-- Independence statements for the blocks of a partition combine into independence of their union.
For a partition `P` of `X` into finite blocks, each block `B` is conditioned on `S ∪ (X \ B)`.
The family of blocks may be infinite, and empty partitions are allowed. -/
def HasGeneralIntersection (R : Set V → Set V → Set V → Prop) : Prop :=
  ∀ (X Y S : Set V) (P : Set (Set V)),
    (∀ B ∈ P, B.Finite) →
    P.PairwiseDisjoint id →
    ⋃₀ P = X →
    (∀ B ∈ P, R B Y (S ∪ (X \ B))) → R X Y S

/-- A semigraphoid satisfying general intersection (P5*). The partition may contain
arbitrarily many finite blocks, including no blocks when `X = ∅`. -/
structure IsGraphoid (R : Set V → Set V → Set V → Prop) : Prop
    extends IsSemigraphoid R where
  /-- General intersection over arbitrary partitions into finite blocks. -/
  intersection : HasGeneralIntersection R


end IndependenceRelation

namespace SimpleGraph

variable {V : Type*}

/-- `G.Separates A B S` means that every walk in `G` from `A` to `B` contains a vertex of `S`,
possibly at an endpoint. -/
def Separates (G : SimpleGraph V) (A B S : Set V) : Prop :=
  ∀ ⦃a b : V⦄, a ∈ A → b ∈ B → ∀ p : G.Walk a b, ∃ v ∈ p.support, v ∈ S

variable {G : SimpleGraph V} {A B C S : Set V}

/-- Separation is symmetric in the two separated sets. -/
theorem Separates.symm (h : G.Separates A B S) : G.Separates B A S := by
  intro b a hb ha p
  obtain ⟨v, hv, hvS⟩ := h ha hb p.reverse
  exact ⟨v, by simpa only [Walk.support_reverse, List.mem_reverse] using hv, hvS⟩

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

variable {V : Type u} (R : Set V → Set V → Set V → Prop) (G : SimpleGraph V)

/-- Any two distinct nonadjacent vertices are independent given all remaining vertices. -/
def IsPairwiseMarkov : Prop :=
  ∀ ⦃i j : V⦄, i ≠ j → ¬ G.Adj i j → R {i} {j} ({i, j}ᶜ)

/-- Each vertex is independent of the vertices outside its closed neighborhood,
given its neighborhood. -/
def IsLocalMarkov : Prop :=
  ∀ i, R {i} (({i} ∪ G.neighborSet i)ᶜ) (G.neighborSet i)

/-- For pairwise disjoint sets `A`, `B`, and `S`, separation of `A` and `B` by `S`
implies their independence given `S`. -/
def IsGlobalMarkov : Prop :=
  ∀ ⦃A B S : Set V⦄, Disjoint A B → Disjoint A S → Disjoint B S →
    G.Separates A B S → R A B S

variable {R G}

/-- The global Markov property implies the local Markov property for any independence relation. -/
theorem IsGlobalMarkov.isLocalMarkov
    (h : IsGlobalMarkov R G) : IsLocalMarkov R G := fun i ↦
  h (by simp) (by simp) (by simp [disjoint_compl_left_iff])
    (G.neighborSet_separates_singleton i)

/-- The local Markov property implies the pairwise Markov property for a semigraphoid. -/
theorem IsLocalMarkov.isPairwiseMarkov
    (hR : IsSemigraphoid R) (h : IsLocalMarkov R G) : IsPairwiseMarkov R G := by
  intro i j hij hadj
  convert hR.weak_union (B := {j}) (C := (({i} ∪ G.neighborSet i)ᶜ \ {j}))
    (by simpa [hij.symm, hadj] using h i) using 1
  apply compl_injective
  simp [compl_sdiff, inter_insert_of_mem, hadj]


/-- General intersection upgrades pairwise Markov to global Markov on any vertex type. -/
theorem IsPairwiseMarkov.isGlobalMarkov
    (hR : IsGraphoid R) (h : IsPairwiseMarkov R G) : IsGlobalMarkov R G := by
  have hI (X Y S : Set V) (hX : ∀ i ∈ X, R {i} Y (S ∪ (X \ {i}))) : R X Y S :=
    hR.intersection X Y S (singleton '' X) (by simp) (pairwiseDisjoint_singleton' X).image
      (by simp) (forall_mem_image.mpr hX)
  intro A B S _ hAS hBS hsep
  let T : Set V := {v | ∃ a ∈ A, ∃ p : G.Walk v a, ∀ w ∈ p.support, w ∉ S}
  let U := Sᶜ \ T
  have hAT : A ⊆ T := fun a ha ↦
    ⟨a, ha, .nil, List.forall_mem_singleton.mpr (hAS.notMem_of_mem_left ha)⟩
  have hBU : B ⊆ U := fun b hb ↦ ⟨hBS.notMem_of_mem_left hb, fun ⟨a, ha, p, hp⟩ ↦
    (hsep.symm hb ha p).elim fun v ⟨hv, hvS⟩ ↦ hp v hv hvS⟩
  refine hR.mono_right (hR.mono_left ?_ hAT) hBU
  refine hI T U S fun i ⟨a, ha, p, hp⟩ ↦ hR.symm (hI U _ _ fun j hj ↦ ?_)
  convert hR.symm (h (fun heq : i = j ↦ hj.2 (heq ▸ ⟨a, ha, p, hp⟩)) ?_) using 1
  · grind [p.start_mem_support]
  · exact fun hadj ↦ hj.2 ⟨a, ha, p.cons hadj.symm, List.forall_mem_cons.mpr ⟨hj.1, hp⟩⟩


end IndependenceRelation

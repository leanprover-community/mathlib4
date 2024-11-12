/-
Copyright (c) 2024 Olivia Röhrig, Christoph Spiegel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Olivia Röhrig, Christoph Spiegel
-/
import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Independent Sets in Graphs

This file defines independent sets (aka cocliques) in simple graphs.
An independent set is a set of vertices that are pairwise nonadjacent.
-/

open Finset

namespace SimpleGraph

variable {α : Type*} (G : SimpleGraph α)

/-! ### Independent Sets -/


section IndependentSet

variable {s : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndependentSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

theorem isIndependentSet_iff : G.IsIndependentSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
theorem isIndependentSet_iff_isClique_of_complement : G.IsIndependentSet s ↔ Gᶜ.IsClique s := by
  rw [isIndependentSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndependentSet s) :=
  decidable_of_iff' _ G.isIndependentSet_iff

-- If `s` is an independent set, its complement meets every edge of `G`.
lemma compl_independentSet_meets_every_edge
    [Fintype α] [DecidableEq α] {s : Finset α} (indA : G.IsIndependentSet s) :
  ∀ e ∈ G.edgeSet, { b ∈ sᶜ | b ∈ e }.Nonempty := by
  rintro ⟨v, w⟩ edgee
  by_contra c
  simp_all [filter_eq_empty_iff, isIndependentSet_iff]
  by_cases vins : v ∈ s
  · have wins : w ∈ s := by by_contra wnins; exact (c wnins).right rfl
    exact (indA vins wins (Adj.ne edgee)) edgee
  · exact (c vins).left rfl

-- The neighbors of a vertex i form an independent set in a trianlge free graph G.
theorem isIndependentSet_neighborSet_if_triangleFree [DecidableEq α] (h: G.CliqueFree 3) (v : α) :
    G.IsIndependentSet (G.neighborSet v) := by
  by_contra nind
  simp [SimpleGraph.IsIndependentSet, Set.Pairwise] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

end IndependentSet

/-! ### N-Independent sets -/


section NIndependentSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-IndependentSet in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
structure IsNIndependentSet (n : ℕ) (s : Finset α) : Prop where
  isIndependentSet : G.IsIndependentSet s
  card_eq : s.card = n

theorem isNIndependentSet_iff : G.IsNIndependentSet n s ↔ G.IsIndependentSet s ∧ s.card = n :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

/-- An independent n-set is an n-clique in the complement graph and vice versa. -/
theorem isNIndependentSet_iff_isNClique_of_complement :
    G.IsNIndependentSet n s ↔ Gᶜ.IsNClique n s := by
  rw [isNIndependentSet_iff, isIndependentSet_iff_isClique_of_complement]
  simp [isNClique_iff]

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNIndependentSet n s) :=
  decidable_of_iff' _ G.isNIndependentSet_iff

end NIndependentSet

/-! ### Graphs without independent sets -/


section IndependentSetFree

variable {n : ℕ}

/-- `G.IndependentSetFree n` means that `G` has no `n`-independent sets. -/
def IndependentSetFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNIndependentSet n t

/-- An graph is 'n'-independent set free iff its complement is n-clique free. -/
theorem isIndependentSetFree_iff_isCliqueFree_of_complement :
    G.IndependentSetFree n ↔ Gᶜ.CliqueFree n := by
  simp [IndependentSetFree, isNIndependentSet_iff_isNClique_of_complement, CliqueFree]

/-- `G.IndependentSetFreeOn s n` means that `G` has no `n`-independent sets contained in `s`. -/
def IndependentSetFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNIndependentSet n t

end IndependentSetFree

/-! ### Set of independent sets-/


section IndependentSetSet

variable {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a set. -/
def independentSetSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNIndependentSet n s }

variable {G}

@[simp]
theorem mem_independentSetSet_iff : s ∈ G.independentSetSet n ↔ G.IsNIndependentSet n s :=
  Iff.rfl

end IndependentSetSet

/-! ### Coclique Number-/


section CocliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
noncomputable def cocliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndependentSet n s}

lemma cocliqueNum_eq_compl_cliqueNum : G.cocliqueNum = Gᶜ.cliqueNum := by
  simp [cliqueNum, ← isNIndependentSet_iff_isNClique_of_complement, cocliqueNum]

theorem IsIndependentSet.card_le_cocliqueNum
    [Fintype α] {t : Finset α} {tc : G.IsIndependentSet t} : #t ≤ G.cocliqueNum := by
  simp [isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement] at *
  exact tc.card_le_cliqueNum

lemma exists_isNIndependentSet_cocliqueNum [Fintype α] :
    ∃ s, G.IsNIndependentSet G.cocliqueNum s := by
  simp [isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement]
  exact exists_isNClique_cliqueNum

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
structure IsMaximumIndependentSet [Fintype α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isIndependentSet : G.IsIndependentSet s
  maximum : ∀ t : Finset α, G.IsIndependentSet t → #t ≤ #s

theorem isMaximumIndependentSet_iff [Fintype α] {s : Finset α} :
    G.IsMaximumIndependentSet s ↔
    G.IsIndependentSet s ∧ ∀ t : Finset α, G.IsIndependentSet t → #t ≤ #s :=
  ⟨fun h ↦ ⟨h.1, h.2⟩, fun h ↦ ⟨h.1, h.2⟩⟩

lemma isMaximumIndependentSet_iff_compl_isMaximumClique [Fintype α] (s : Finset α)  :
    G.IsMaximumIndependentSet s ↔ Gᶜ.IsMaximumClique s := by
  simp [isMaximumIndependentSet_iff, isIndependentSet_iff_isClique_of_complement,
  isMaximumClique_iff]

/-- An independent set in a graph `G` that cannot be extended by adding more vertices. -/
theorem isMaximalIndependentSet_iff {s : Set α} :
    Maximal G.IsIndependentSet s ↔
    G.IsIndependentSet s ∧ ∀ t : Set α, G.IsIndependentSet t → s ⊆ t → t ⊆ s :=
  Iff.rfl

lemma isMaximalIndependentSet_iff_compl_isMaximalClique (s : Finset α)  :
    Maximal G.IsIndependentSet s ↔ Maximal Gᶜ.IsClique s := by
  simp [isMaximalIndependentSet_iff, isIndependentSet_iff_isClique_of_complement,
  isMaximalClique_iff]

lemma IsMaximumIndependentSet.isMaximalIndependentSet
    [Fintype α] (s : Finset α) (M : G.IsMaximumIndependentSet s) :
    Maximal G.IsIndependentSet s := by
  rw [isMaximalIndependentSet_iff_compl_isMaximalClique]
  rw [isMaximumIndependentSet_iff_compl_isMaximumClique] at M
  exact IsMaximumClique.isMaximalClique s M

theorem maximumIndependentSet_card_eq_cocliqueNum
    [Fintype α] (t : Finset α) (tmc : G.IsMaximumIndependentSet t) : #t = G.cocliqueNum := by
  simp [isMaximumIndependentSet_iff, isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement, ← isMaximumClique_iff] at *
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

lemma maximumIndependentSet_exists [Fintype α] : ∃ (s : Finset α), G.IsMaximumIndependentSet s := by
  simp [isMaximumIndependentSet_iff_compl_isMaximumClique, maximumClique_exists]

end CocliqueNumber

/-! ### Finset of independent sets -/


section IndependentSetFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

/-- The `n`-independentSets in a graph as a finset. -/
def independentSetFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNIndependentSet n s}

variable {G} in
@[simp]
theorem mem_independentSetFinset_iff : s ∈ G.independentSetFinset n ↔ G.IsNIndependentSet n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

end IndependentSetFinset

end SimpleGraph

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


section IndepSet

variable {s : Set α}

/-- An independent set in a graph is a set of vertices that are pairwise not adjacent. -/
abbrev IsIndepSet (s : Set α) : Prop :=
  s.Pairwise (fun v w ↦ ¬G.Adj v w)

theorem isIndepSet_iff : G.IsIndepSet s ↔ s.Pairwise (fun v w ↦ ¬G.Adj v w) :=
  Iff.rfl

/-- An independent set is a clique in the complement graph and vice versa. -/
theorem isIndepSet_iff_isClique_of_complement : G.IsIndepSet s ↔ Gᶜ.IsClique s := by
  rw [isIndepSet_iff, isClique_iff]; repeat rw [Set.Pairwise]
  simp_all [compl_adj]

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndepSet s) :=
  decidable_of_iff' _ G.isIndepSet_iff

-- If `s` is an independent set, its complement meets every edge of `G`.
lemma compl_indepSet_meets_every_edge
    [Fintype α] [DecidableEq α] {s : Finset α} (indA : G.IsIndepSet s) :
  ∀ e ∈ G.edgeSet, { b ∈ sᶜ | b ∈ e }.Nonempty := by
  rintro ⟨v, w⟩ edgee
  by_contra c
  simp_all [filter_eq_empty_iff, isIndepSet_iff]
  by_cases vins : v ∈ s
  · have wins : w ∈ s := by by_contra wnins; exact (c wnins).right rfl
    exact (indA vins wins (Adj.ne edgee)) edgee
  · exact (c vins).left rfl

-- The neighbors of a vertex `v` form an independent set in a triangle free graph `G`.
theorem isIndepSet_neighborSet_of_triangleFree [DecidableEq α] (h: G.CliqueFree 3) (v : α) :
    G.IsIndepSet (G.neighborSet v) := by
  by_contra nind
  simp [SimpleGraph.IsIndepSet, Set.Pairwise] at nind
  obtain ⟨j, avj, k, avk, _, ajk⟩ := nind
  exact h {v, j, k} (is3Clique_triple_iff.mpr (by simp [avj, avk, ajk]))

end IndepSet

/-! ### N-Independent sets -/


section NIndepSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-independent set in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
@[mk_iff]
structure IsNIndepSet (n : ℕ) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  card_eq : s.card = n

/-- An `n`-independent set is an `n`-clique in the complement graph and vice versa. -/
theorem isNIndepSet_iff_isNClique_of_complement : G.IsNIndepSet n s ↔ Gᶜ.IsNClique n s := by
  rw [isNIndepSet_iff, isIndepSet_iff_isClique_of_complement]
  simp [isNClique_iff]

instance [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α} :
    Decidable (G.IsNIndepSet n s) :=
  decidable_of_iff' _ (G.isNIndepSet_iff n s)

end NIndepSet

/-! ### Graphs without independent sets -/


section IndepSetFree

variable {n : ℕ}

/-- `G.IndepSetFree n` means that `G` has no `n`-independent sets. -/
def IndepSetFree (n : ℕ) : Prop :=
  ∀ t, ¬G.IsNIndepSet n t

/-- An graph is `n`-independent set free iff its complement is `n`-clique free. -/
theorem indepSetFree_iff_cliqueFree_of_complement : G.IndepSetFree n ↔ Gᶜ.CliqueFree n := by
  simp [IndepSetFree, isNIndepSet_iff_isNClique_of_complement, CliqueFree]

/-- `G.IndepSetFreeOn s n` means that `G` has no `n`-independent sets contained in `s`. -/
def IndepSetFreeOn (G : SimpleGraph α) (s : Set α) (n : ℕ) : Prop :=
  ∀ ⦃t⦄, ↑t ⊆ s → ¬G.IsNIndepSet n t

end IndepSetFree

/-! ### Set of independent sets-/


section IndepSetSet

variable {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a set. -/
def indepSetSet (n : ℕ) : Set (Finset α) :=
  { s | G.IsNIndepSet n s }

variable {G}

@[simp]
theorem mem_indepSetSet_iff : s ∈ G.indepSetSet n ↔ G.IsNIndepSet n s :=
  Iff.rfl

end IndepSetSet

/-! ### Independence Number-/


section IndepNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
noncomputable def indepNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndepSet n s}

@[simp]
lemma cliqueNum_compl : G.cliqueNum = Gᶜ.indepNum := by
  simp [indepNum, isNIndepSet_iff_isNClique_of_complement, cliqueNum]

@[simp]
lemma indepNum_compl : G.indepNum = Gᶜ.cliqueNum := by
  simp [cliqueNum, ← isNIndepSet_iff_isNClique_of_complement, indepNum]

theorem IsIndepSet.card_le_indepNum
    [Fintype α] {t : Finset α} {tc : G.IsIndepSet t} : #t ≤ G.indepNum := by
  simp [isIndepSet_iff_isClique_of_complement, indepNum,
  isNIndepSet_iff_isNClique_of_complement] at *
  exact tc.card_le_cliqueNum

lemma exists_isNIndepSet_indepNum [Fintype α] : ∃ s, G.IsNIndepSet G.indepNum s := by
  simp [isIndepSet_iff_isClique_of_complement, indepNum,
  isNIndepSet_iff_isNClique_of_complement]
  exact exists_isNClique_cliqueNum

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
@[mk_iff]
structure IsMaximumIndepSet [Fintype α] (G : SimpleGraph α) (s : Finset α) : Prop where
  isIndepSet : G.IsIndepSet s
  maximum : ∀ t : Finset α, G.IsIndepSet t → #t ≤ #s

lemma isMaximumIndepSet_iff_compl_isMaximumClique [Fintype α] (s : Finset α) :
    G.IsMaximumIndepSet s ↔ Gᶜ.IsMaximumClique s := by
  simp [isMaximumIndepSet_iff, isIndepSet_iff_isClique_of_complement,
  isMaximumClique_iff]

/-- An independent set in a graph `G` that cannot be extended by adding more vertices. -/
theorem isMaximalIndepSet_iff {s : Set α} :
    Maximal G.IsIndepSet s ↔ G.IsIndepSet s ∧ ∀ t : Set α, G.IsIndepSet t → s ⊆ t → t ⊆ s :=
  Iff.rfl

lemma isMaximalIndepSet_iff_compl_isMaximalClique (s : Finset α) :
    Maximal G.IsIndepSet s ↔ Maximal Gᶜ.IsClique s := by
  simp [isMaximalIndepSet_iff, isIndepSet_iff_isClique_of_complement,
  isMaximalClique_iff]

lemma IsMaximumIndepSet.isMaximalIndepSet
    [Fintype α] (s : Finset α) (M : G.IsMaximumIndepSet s) : Maximal G.IsIndepSet s := by
  rw [isMaximalIndepSet_iff_compl_isMaximalClique]
  rw [isMaximumIndepSet_iff_compl_isMaximumClique] at M
  exact IsMaximumClique.isMaximalClique s M

theorem maximumIndepSet_card_eq_indepNum
    [Fintype α] (t : Finset α) (tmc : G.IsMaximumIndepSet t) : #t = G.indepNum := by
  simp [isMaximumIndepSet_iff, isIndepSet_iff_isClique_of_complement, indepNum,
  isNIndepSet_iff_isNClique_of_complement, ← isMaximumClique_iff] at *
  exact Gᶜ.maximumClique_card_eq_cliqueNum t tmc

lemma maximumIndepSet_exists [Fintype α] : ∃ (s : Finset α), G.IsMaximumIndepSet s := by
  simp [isMaximumIndepSet_iff_compl_isMaximumClique, maximumClique_exists]

end IndepNumber

/-! ### Finset of independent sets -/


section IndepSetFinset

variable [Fintype α] [DecidableEq α] [DecidableRel G.Adj] {n : ℕ} {s : Finset α}

/-- The `n`-independent sets in a graph as a finset. -/
def indepSetFinset (n : ℕ) : Finset (Finset α) := {s | G.IsNIndepSet n s}

variable {G} in
@[simp]
theorem mem_indepSetFinset_iff : s ∈ G.indepSetFinset n ↔ G.IsNIndepSet n s :=
  mem_filter.trans <| and_iff_right <| mem_univ _

end IndepSetFinset

end SimpleGraph

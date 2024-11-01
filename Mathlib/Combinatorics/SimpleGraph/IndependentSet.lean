import Mathlib.Data.Finset.Pairwise
import Mathlib.Combinatorics.SimpleGraph.Clique


/-!
# Independent Sets in Graphs

This file defines independent sets (aka cocliques) in simple graphs.
An independent set is a set of vertices that are pairwise nonadjacent.

-/

open Finset Fintype Function

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
  simp_all only [compl_adj, ne_eq, not_false_eq_true, true_and]

instance [DecidableEq α] [DecidableRel G.Adj] {s : Finset α} : Decidable (G.IsIndependentSet s) :=
  decidable_of_iff' _ G.isIndependentSet_iff

end IndependentSet

/-! ### N-Independent sets -/

section NIndependentSet

variable {n : ℕ} {s : Finset α}

/-- An `n`-IndependentSet in a graph is a set of `n` vertices which are pairwise nonadjacent. -/
structure IsNIndependentSet (n : ℕ) (s : Finset α) : Prop where
  IndependentSet : G.IsIndependentSet s
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

end IndependentSetFree

/-! ### Coclique Number and extremal Independent Sets -/

section CocliqueNumber

variable {α : Type*} {G : SimpleGraph α}

/-- The maximal number of vertices of an independent set in a graph `G`. -/
noncomputable def cocliqueNum (G : SimpleGraph α) : ℕ := sSup {n | ∃ s, G.IsNIndependentSet n s}

lemma cocliqueNum_eq_compl_cliqueNum : G.cocliqueNum = Gᶜ.cliqueNum := by
  simp [cliqueNum, ← isNIndependentSet_iff_isNClique_of_complement, cocliqueNum]

/-- An independent set in a graph `G` such that there is no independent set with more vertices. -/
def isMaximumIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsIndependentSet s ∧ ∀ (t : Finset α), G.IsIndependentSet t → #t ≤ #s

lemma isMaximumIndependentSet_iff_compl_isMaximumClique (s : Finset α)  :
    G.isMaximumIndependentSet s ↔ Gᶜ.isMaximumClique s := by
  simp [isMaximumIndependentSet, isIndependentSet_iff_isClique_of_complement] at *
  exact Iff.symm (Eq.to_iff rfl)

/-- An independent set in a graph `G` that cannot be extended by adding vertices. -/
def isMaximalIndependentSet (G : SimpleGraph α) (s : Finset α) : Prop :=
  G.IsIndependentSet s ∧ ¬ ∃ (t : Finset α), G.IsIndependentSet t ∧ s ⊂ t

lemma isMaximalIndependentSet_iff_compl_isMaximalClique (s : Finset α)  :
    G.isMaximalIndependentSet s ↔ Gᶜ.isMaximalClique s := by
  simp [isMaximalIndependentSet, isIndependentSet_iff_isClique_of_complement, ← not_and,
  ← not_exists] at *
  exact Iff.symm (Eq.to_iff rfl)

-- these are the thms i need for mantel proof
variable [fin : Fintype α]

theorem independentSet_card_le_cocliqueNum (t : Finset α) (tc : G.IsIndependentSet t) :
    #t ≤ G.cocliqueNum := by
  simp [isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement] at *
  exact clique_card_le_cliqueNum t tc

theorem maximumIndependentSet_card_eq_cocliqueNum
    (t : Finset α) (tmc : G.isMaximumIndependentSet t) : #t = G.cocliqueNum := by
  simp [isMaximumIndependentSet, isIndependentSet_iff_isClique_of_complement, cocliqueNum,
  isNIndependentSet_iff_isNClique_of_complement] at *
  exact maximumClique_card_eq_cliqueNum t tmc
end CocliqueNumber

end SimpleGraph

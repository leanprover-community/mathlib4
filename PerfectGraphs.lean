import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Combinatorics.SimpleGraph.Coloring

variable {V : Type*} {G : SimpleGraph V}

namespace SimpleGraph

def IsPerfectGraph (G : SimpleGraph V) : Prop :=
  ∀ s : Set V, (G.induce s).chromaticNumber = (G.induce s).cliqueNum

theorem perfect_iff_subgraph_perfect :
  G.IsPerfectGraph ↔ ∀ s : Set V, (G.induce s).IsPerfectGraph := by
  constructor
  · rw [IsPerfectGraph]
    intros h1 _ h3

    sorry
  · sorry


variable [Fintype V] [DecidableEq V] in
theorem perfect_iff_subgraph_has_vast_independent_set :
  G.IsPerfectGraph ↔ ∀ H ≤ G, ∃ s : Finset V,
  (H.IsIndepSet s ∧ (∀ t : Finset V, H.IsMaximumClique t → (t ∩ s) ≠ ∅)) := by
  constructor
  · intros h1 h2 h3
    rw [IsPerfectGraph] at h1
    sorry
  · sorry

theorem perfect_iff_complement_perfect :
  G.IsPerfectGraph ↔ Gᶜ.IsPerfectGraph := by sorry


end SimpleGraph

import Mathlib.Combinatorics.SimpleGraph.Basic

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/--
The line graph of a simple graph `G` has its vertex set as the edges of `G`, and two vertices of
the line graph are adjacent if the corresponding edges share a vertex in `G`.
-/
@[simps]
def lineGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj e₁ e₂ := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
  symm e₁ e₂ := by intro h; rwa [ne_comm, Set.inter_comm]

lemma lineGraph_adj_iff_exists {e₁ e₂ : G.edgeSet} :
    (G.lineGraph).Adj e₁ e₂ ↔ e₁ ≠ e₂ ∧ ∃ v, v ∈ (e₁ : Sym2 V) ∧ v ∈ (e₂ : Sym2 V) := by
  simp [Set.Nonempty]

@[simp] lemma lineGraph_bot : (⊥ : SimpleGraph V).lineGraph = ⊥ := by aesop

end SimpleGraph

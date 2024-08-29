import Mathlib.Combinatorics.SimpleGraph.Basic

def SimpleGraph.LineGraph {V : Type*} (G : SimpleGraph V) : SimpleGraph G.edgeSet where
  Adj (e₁ e₂) := e₁ ≠ e₂ ∧ (e₁ ∩ e₂ : Set V).Nonempty
  symm e₁ e₂ := by intro h; rwa [ne_comm, Set.inter_comm]

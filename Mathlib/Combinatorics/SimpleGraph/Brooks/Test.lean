import Mathlib.Combinatorics.SimpleGraph.Subgraph

variable {α : Type*} (G : SimpleGraph α)

namespace SimpleGraph

abbrev edgesIn (s : Set α) [Fintype (G.induce s).edgeSet] : ℕ :=
  (G.induce s).edgeSet.toFinset.card

lemma edgesIn_eq (s : Set α) (h : ∃ a, a ∈ s) [Fintype (G.induce s).edgeSet] :
    G.edgesIn s = (G.induce s).edgeSet.toFinset.card := rfl

lemma edgesIn_eq' (s : Finset α) (h : ∃ a, a ∈ s) [Fintype (G.induce s).edgeSet] :
    G.edgesIn s = (G.induce s).edgeSet.toFinset.card :=
  G.edgesIn_eq _ (by exact h)
  -- failed to synthesize Fintype ↑(induce (Membership.mem s.val) G).edgeSet
  --  G.degreeIn_eq' s h -- Goals accomplished!

end SimpleGraph

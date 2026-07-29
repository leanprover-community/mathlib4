import Mathlib.Probability.Combinatorics.BinomialRandomGraph.Defs

open MeasureTheory Measure ProbabilityTheory unitInterval

namespace SimpleGraph
variable {V : Type*} {p : I}

-- This should be restated as an equality of distributions once
-- https://github.com/leanprover-community/mathlib4/pull/28248 is in.
proof_wanted binomialRandom_map_ncard_edgeSet_singleton [Finite V] (n : ℕ) :
    G(V, p).map (fun G ↦ G.edgeSet.ncard) {n} = ((Nat.card V).choose 2).choose n * toNNReal p ^ n *
      toNNReal (σ p) ^ ((Nat.card V).choose 2 - n)

end SimpleGraph

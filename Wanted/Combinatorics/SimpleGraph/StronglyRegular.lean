import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

universe u

namespace SimpleGraph

variable {V : Type u} [Fintype V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {G}

/-- **Conway's 99-graph problem** (from https://oeis.org/A248380/a248380.pdf)
can be reformulated as the existence of a strongly regular graph with params (99, 14, 1, 2).
This is an open problem, and has no known proof of existence. -/
proof_wanted conway_99 : ∃ α : Type*, ∃ (g : SimpleGraph α), IsSRGWith G 99 14 1 2

end SimpleGraph

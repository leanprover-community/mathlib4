/-
Copyright (c) 2025 Tristan Figueroa-Reid. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristan Figueroa-Reid
-/
module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular

namespace SimpleGraph

/-- **Conway's 99-graph problem** (from https://oeis.org/A248380/a248380.pdf)
can be reformulated as the existence of a strongly regular graph with params (99, 14, 1, 2).
This is an open problem, and has no known proof of existence. -/
proof_wanted conway_99 : ∃ (α : Type) (_ : Fintype α) (G : SimpleGraph α) (_ : DecidableRel G.Adj),
    IsSRGWith G 99 14 1 2

end SimpleGraph

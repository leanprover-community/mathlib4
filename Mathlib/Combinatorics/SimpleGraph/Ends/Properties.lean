/-
Copyright (c) 2022 Anand Rao, Rémi Bottinelli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anand Rao, Rémi Bottinelli
-/
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs

#align_import combinatorics.simple_graph.ends.properties from "leanprover-community/mathlib"@"db53863fb135228820ee0b08e8dce9349a3d911b"

/-!
# Properties of the ends of graphs

This file is meant to contain results about the ends of (locally finite connected) graphs.

-/


variable {V : Type} (G : SimpleGraph V)

namespace SimpleGraph

instance [Finite V] : IsEmpty G.end :=
  ⟨by
    rintro ⟨s, _⟩
    cases nonempty_fintype V
    obtain ⟨v, h⟩ := (s <| Opposite.op Finset.univ).nonempty
    exact
      Set.disjoint_iff.mp (s _).disjoint_right
        ⟨by simp only [Opposite.unop_op, Finset.coe_univ, Set.mem_univ], h⟩⟩

end SimpleGraph

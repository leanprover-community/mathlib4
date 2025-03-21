import Mathlib.Topology.Maps.Basic
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

section homeo

theorem Homeomorph.discreteTopology {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology X] (h : X ≃ₜ Y) :
    DiscreteTopology Y :=
  h.symm.isEmbedding.discreteTopology

#find_home Homeomorph.discreteTopology

end homeo

section finrank

open Submodule

theorem Set.finrank_empty (R : Type*) {M : Type*} [Ring R] [Nontrivial R]
    [AddCommGroup M] [Module R M] :
    Set.finrank R (∅ : Set M) = 0 := by
  rw [Set.finrank, span_empty, finrank_bot]

#find_home!  Set.finrank_empty
end finrank

/-
Copyright (c) 2026 Max Feldman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Max Feldman
-/
module

public import Mathlib.Basic.Rel
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Closed graphs and continuity

We relate continuity of a function `f : X → Y` between topological spaces to closedness of its
graph `Function.graph f : Set (X × Y)`.

## Main results

* `Continuous.isClosed_graph`: a continuous function into a Hausdorff space has a closed graph.
* `continuous_of_isClosed_graph`: a function into a compact space with a closed graph is
  continuous.
* `continuous_iff_isClosed_graph`: a function into a compact Hausdorff space is continuous if and
  only if its graph is closed.

For the closed graph theorem of functional analysis, about linear maps between Banach spaces, see
`LinearMap.continuous_of_isClosed_graph`.
-/

@[expose] public section

open Set

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y}

/-- The graph of a continuous function into a Hausdorff space is closed. -/
theorem Continuous.isClosed_graph [T2Space Y] (hf : Continuous f) : IsClosed f.graph :=
  isClosed_eq (hf.comp continuous_fst) continuous_snd

/-- A function into a compact space with a closed graph is continuous. -/
theorem continuous_of_isClosed_graph [CompactSpace Y] (hf : IsClosed f.graph) : Continuous f := by
  rw [continuous_iff_isClosed]
  intro C hC
  have h : f ⁻¹' C = Prod.fst '' (f.graph ∩ univ ×ˢ C) := by
    ext x
    simp [Function.graph]
  rw [h]
  exact isClosedMap_fst_of_compactSpace _ (hf.inter (isClosed_univ.prod hC))

/-- A function into a compact Hausdorff space is continuous if and only if its graph is closed. -/
theorem continuous_iff_isClosed_graph [CompactSpace Y] [T2Space Y] :
    Continuous f ↔ IsClosed f.graph :=
  ⟨Continuous.isClosed_graph, continuous_of_isClosed_graph⟩

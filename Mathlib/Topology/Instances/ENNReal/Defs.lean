/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Instances.NNReal.Defs

/-!
# Topology on extended non-negative reals

This file provides the absolutely minimal properties of the topology on the extended non-negative
real numbers: its definition and a proof that its embedding into `ℝ≥0` is continuous.

Further results can be found in `Mathlib/Topology/Instances/ENNReal/Basic.lean`.
-/

noncomputable section

open Metric Set Topology
open scoped NNReal

namespace ENNReal

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, while this topology doesn't have singleton elements. -/
instance : TopologicalSpace ℝ≥0∞ := Preorder.topology ℝ≥0∞

instance : OrderTopology ℝ≥0∞ := ⟨rfl⟩

theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩

end ENNReal

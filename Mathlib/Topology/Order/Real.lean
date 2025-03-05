/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Data.Real.EReal
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.Topology.Order.LeftRightNhds
import Mathlib.Topology.Order.T5

/-!
# The reals are equipped with their order topology

The topologies on `ℝ` and `ℝ≥0` are defined via the `PseudoMetricSpace` instances
found in `Mathlib.Topology.MetricSpace.Pseudo.Defs` and
`Mathlib.Topology.MetricSpace.Pseudo.Constructions` respectively.
-/

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

open Set

open Bornology Filter Metric Set
open scoped NNReal Topology

instance : OrderTopology ℝ :=
  orderTopology_of_nhds_abs fun x => by
    simp only [nhds_basis_ball.eq_biInf, ball, Real.dist_eq, abs_sub_comm]

namespace EReal

/-!
### Topological structure on `EReal`

We endow `EReal` with the order topology.
Most proofs are adapted from the corresponding proofs on `ℝ≥0∞`.
-/

instance : TopologicalSpace EReal := Preorder.topology EReal
instance : OrderTopology EReal := ⟨rfl⟩

instance : T5Space EReal := inferInstance
instance : T2Space EReal := inferInstance

lemma denseRange_ratCast : DenseRange (fun r : ℚ ↦ ((r : ℝ) : EReal)) :=
  dense_of_exists_between fun _ _ h => exists_range_iff.2 <| exists_rat_btwn_of_lt h

end EReal

namespace ENNReal

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, while this topology doesn't have singleton elements. -/
instance : TopologicalSpace ℝ≥0∞ := Preorder.topology ℝ≥0∞

instance : OrderTopology ℝ≥0∞ := ⟨rfl⟩

-- short-circuit type class inference
instance : T2Space ℝ≥0∞ := inferInstance
instance : T5Space ℝ≥0∞ := inferInstance
instance : T4Space ℝ≥0∞ := inferInstance

end ENNReal

namespace NNReal

/-!
Instances for the following typeclasses are defined:

* `OrderTopology ℝ≥0`

Everything is inherited from the corresponding structures on the reals.
-/

instance : OrderTopology ℝ≥0 :=
  orderTopology_of_ordConnected (t := Ici 0)

end NNReal

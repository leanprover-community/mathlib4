/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Topology.MetricSpace.ProperSpace
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Order.MonotoneContinuity
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.UniformSpace.Real

/-!
# Second countability of the reals

We prove that `EReal`, `ℝ≥0` and `ℝ≥0∞` are second countable.
In the process, we also provide the instance `ProperSpace ℝ≥0`.
-/

@[expose] public section

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

noncomputable section

open Set Topology TopologicalSpace

namespace EReal

instance : SecondCountableTopology EReal :=
  have : SeparableSpace EReal := ⟨⟨_, countable_range _, denseRange_ratCast⟩⟩
  .of_separableSpace_orderTopology _

end EReal

namespace NNReal

/-!
Instances for `ℝ≥0` are inherited from the corresponding structures on the reals.
-/

instance : SecondCountableTopology ℝ≥0 :=
  inferInstanceAs (SecondCountableTopology { x : ℝ | 0 ≤ x })

instance instProperSpace : ProperSpace ℝ≥0 where
  isCompact_closedBall x r := by
    have emb : IsClosedEmbedding ((↑) : ℝ≥0 → ℝ) := Isometry.isClosedEmbedding fun _ ↦ congrFun rfl
    exact emb.isCompact_preimage (K := Metric.closedBall x r) (isCompact_closedBall _ _)

end NNReal

namespace ENNReal

instance : SecondCountableTopology ℝ≥0∞ :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology

end ENNReal

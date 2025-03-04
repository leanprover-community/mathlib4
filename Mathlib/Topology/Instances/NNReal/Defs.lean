/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.Instances.Real.Defs
import Mathlib.Topology.MetricSpace.Isometry

/-!
# Topology on `ℝ≥0`

The natural topology on `ℝ≥0` (the one induced from `ℝ`), and a basic API.

## Main definitions

Instances for the following typeclasses are defined:

* `TopologicalSpace ℝ≥0`
* `IsTopologicalSemiring ℝ≥0`
* `SecondCountableTopology ℝ≥0`
* `OrderTopology ℝ≥0`
* `ProperSpace ℝ≥0`
* `ContinuousSub ℝ≥0`
* `HasContinuousInv₀ ℝ≥0` (continuity of `x⁻¹` away from `0`)
* `ContinuousSMul ℝ≥0 α` (whenever `α` has a continuous `MulAction ℝ α`)

Everything is inherited from the corresponding structures on the reals.

-/

noncomputable section

open Filter Metric Set TopologicalSpace Topology

namespace NNReal

instance : TopologicalSpace ℝ≥0 := inferInstance

-- short-circuit type class inference
instance : IsTopologicalSemiring ℝ≥0 where
  toContinuousAdd := continuousAdd_induced toRealHom
  toContinuousMul := continuousMul_induced toRealHom

instance : SecondCountableTopology ℝ≥0 :=
  inferInstanceAs (SecondCountableTopology { x : ℝ | 0 ≤ x })

instance : OrderTopology ℝ≥0 :=
  orderTopology_of_ordConnected (t := Ici 0)

instance : CompleteSpace ℝ≥0 :=
  isClosed_Ici.completeSpace_coe

theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ) :=
  continuous_subtype_val

instance : ContinuousSub ℝ≥0 :=
  ⟨((continuous_coe.fst'.sub continuous_coe.snd').max continuous_const).subtype_mk _⟩

instance : HasContinuousInv₀ ℝ≥0 := inferInstance

variable {α : Type*}

instance [TopologicalSpace α] [MulAction ℝ α] [ContinuousSMul ℝ α] :
    ContinuousSMul ℝ≥0 α where
  continuous_smul := continuous_induced_dom.fst'.smul continuous_snd

/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps (config := .asFn)]
def _root_.ContinuousMap.coeNNRealReal : C(ℝ≥0, ℝ) :=
  ⟨(↑), continuous_coe⟩

@[simp]
lemma coeNNRealReal_zero : ContinuousMap.coeNNRealReal 0 = 0 := rfl

instance ContinuousMap.canLift {X : Type*} [TopologicalSpace X] :
    CanLift C(X, ℝ) C(X, ℝ≥0) ContinuousMap.coeNNRealReal.comp fun f => ∀ x, 0 ≤ f x where
  prf f hf := ⟨⟨fun x => ⟨f x, hf x⟩, f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩

instance instProperSpace : ProperSpace ℝ≥0 where
  isCompact_closedBall x r := by
    have emb : IsClosedEmbedding ((↑) : ℝ≥0 → ℝ) := Isometry.isClosedEmbedding fun _ ↦ congrFun rfl
    exact emb.isCompact_preimage (K := Metric.closedBall x r) (isCompact_closedBall _ _)

end NNReal

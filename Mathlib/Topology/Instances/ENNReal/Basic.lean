/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Instances.ENNReal.Defs
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.T5

/-!
# Topology on extended non-negative reals
-/

noncomputable section

open Filter Topology
open scoped NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

open TopologicalSpace

/-- Properties of the topology on `ℝ≥0∞`. -/


-- short-circuit type class inference
instance : T2Space ℝ≥0∞ := inferInstance
instance : T5Space ℝ≥0∞ := inferInstance
instance : T4Space ℝ≥0∞ := inferInstance

instance : SecondCountableTopology ℝ≥0∞ :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology

instance : MetrizableSpace ENNReal :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

instance : ContinuousAdd ℝ≥0∞ := by
  refine ⟨continuous_iff_continuousAt.2 ?_⟩
  rintro ⟨_ | a, b⟩
  · exact tendsto_nhds_top_mono' continuousAt_fst fun p => le_add_right le_rfl
  rcases b with (_ | b)
  · exact tendsto_nhds_top_mono' continuousAt_snd fun p => le_add_left le_rfl
  simp only [ContinuousAt, some_eq_coe, nhds_coe_coe, ← coe_add, tendsto_map'_iff,
    Function.comp_def, tendsto_coe, tendsto_add]

instance : ContinuousInv ℝ≥0∞ := ⟨OrderIso.invENNReal.continuous⟩

end ENNReal

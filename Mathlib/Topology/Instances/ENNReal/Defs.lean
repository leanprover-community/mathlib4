/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.Order.T5
import Mathlib.Topology.Instances.NNReal.Defs

/-!
# Topology on extended non-negative reals
-/

noncomputable section

open Filter Function Metric Set Topology
open scoped Finset ENNReal NNReal

variable {α : Type*} {β : Type*} {γ : Type*}

namespace ENNReal

variable {a b : ℝ≥0∞} {r : ℝ≥0} {x : ℝ≥0∞} {ε : ℝ≥0∞}

open TopologicalSpace

/-- Topology on `ℝ≥0∞`.

Note: this is different from the `EMetricSpace` topology. The `EMetricSpace` topology has
`IsOpen {∞}`, while this topology doesn't have singleton elements. -/
instance : TopologicalSpace ℝ≥0∞ := Preorder.topology ℝ≥0∞

instance : OrderTopology ℝ≥0∞ := ⟨rfl⟩

-- short-circuit type class inference
instance : T2Space ℝ≥0∞ := inferInstance
instance : T5Space ℝ≥0∞ := inferInstance
instance : T4Space ℝ≥0∞ := inferInstance

instance : SecondCountableTopology ℝ≥0∞ :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.secondCountableTopology

instance : MetrizableSpace ENNReal :=
  orderIsoUnitIntervalBirational.toHomeomorph.isEmbedding.metrizableSpace

theorem isEmbedding_coe : IsEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  coe_strictMono.isEmbedding_of_ordConnected <| by rw [range_coe']; exact ordConnected_Iio

@[norm_cast]
theorem tendsto_coe {f : Filter α} {m : α → ℝ≥0} {a : ℝ≥0} :
    Tendsto (fun a => (m a : ℝ≥0∞)) f (𝓝 ↑a) ↔ Tendsto m f (𝓝 a) :=
  isEmbedding_coe.tendsto_nhds_iff.symm

theorem isOpenEmbedding_coe : IsOpenEmbedding ((↑) : ℝ≥0 → ℝ≥0∞) :=
  ⟨isEmbedding_coe, by rw [range_coe']; exact isOpen_Iio⟩

theorem nhds_coe_coe {r p : ℝ≥0} :
    𝓝 ((r : ℝ≥0∞), (p : ℝ≥0∞)) = (𝓝 (r, p)).map fun p : ℝ≥0 × ℝ≥0 => (↑p.1, ↑p.2) :=
  ((isOpenEmbedding_coe.prodMap isOpenEmbedding_coe).map_nhds_eq (r, p)).symm

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

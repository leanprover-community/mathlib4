/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Topology.MetricSpace.Cauchy

/-!
# The reals are complete

This file provides the instances `CompleteSpace ℝ` and `CompleteSpace ℝ≥0`.
Along the way, we add a shortcut instance for the natural topology on `ℝ≥0`
(the one induced from `ℝ`), and add some basic API.
-/

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

noncomputable section

open Filter Metric Set

instance Real.instCompleteSpace : CompleteSpace ℝ := by
  apply complete_of_cauchySeq_tendsto
  intro u hu
  let c : CauSeq ℝ abs := ⟨u, Metric.cauchySeq_iff'.1 hu⟩
  refine ⟨c.lim, fun s h => ?_⟩
  rcases Metric.mem_nhds_iff.1 h with ⟨ε, ε0, hε⟩
  have := c.equiv_lim ε ε0
  simp only [mem_map, mem_atTop_sets]
  exact this.imp fun N hN n hn => hε (hN n hn)

namespace NNReal

/-!
### Topology on `ℝ≥0`
All the instances are inherited from the corresponding structures on the reals.

-/

instance : TopologicalSpace ℝ≥0 := inferInstance

instance : CompleteSpace ℝ≥0 :=
  isClosed_Ici.completeSpace_coe

theorem continuous_coe : Continuous ((↑) : ℝ≥0 → ℝ) :=
  continuous_subtype_val

/-- Embedding of `ℝ≥0` to `ℝ` as a bundled continuous map. -/
@[simps -fullyApplied]
def _root_.ContinuousMap.coeNNRealReal : C(ℝ≥0, ℝ) :=
  ⟨(↑), continuous_coe⟩

@[simp]
lemma coeNNRealReal_zero : ContinuousMap.coeNNRealReal 0 = 0 := rfl

instance ContinuousMap.canLift {X : Type*} [TopologicalSpace X] :
    CanLift C(X, ℝ) C(X, ℝ≥0) ContinuousMap.coeNNRealReal.comp fun f => ∀ x, 0 ≤ f x where
  prf f hf := ⟨⟨fun x => ⟨f x, hf x⟩, f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩

end NNReal

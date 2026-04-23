/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Nat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Map
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# The reals are complete

This file provides the instances `CompleteSpace ℝ` and `CompleteSpace ℝ≥0`.
Along the way, we add a shortcut instance for the natural topology on `ℝ≥0`
(the one induced from `ℝ`), and add some basic API.
-/

@[expose] public section

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

@[fun_prop]
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
  prf f hf := ⟨⟨fun x => .mk (f x) (hf x), f.2.subtype_mk _⟩, DFunLike.ext' rfl⟩

end NNReal

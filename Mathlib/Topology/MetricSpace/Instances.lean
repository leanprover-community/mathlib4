/-
Copyright (c) 2015, 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.PseudoMetric.Instances

/-!
# Metric space instances

Instance for `Empty`, `PUnit`, `ℝ`, and derived instances `ULift`, products, and pi types.
-/

open Filter
open scoped NNReal Uniformity

universe u v w

variable {α : Type u} {β : Type v} [PseudoMetricSpace α] {γ : Type w} [MetricSpace γ]

@[to_additive]
instance {α : Type*} [MetricSpace α] : MetricSpace αᵐᵒᵖ :=
  MetricSpace.induced MulOpposite.unop MulOpposite.unop_injective ‹_›

instance : MetricSpace Empty where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  edist_dist _ _ := ENNReal.ofReal_zero.symm -- Porting note: should not be needed
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := Subsingleton.elim _ _

instance : MetricSpace PUnit.{u + 1} where
  dist _ _ := 0
  dist_self _ := rfl
  dist_comm _ _ := rfl
  edist _ _ := 0
  edist_dist _ _ := ENNReal.ofReal_zero.symm -- Porting note: should not be needed
  eq_of_dist_eq_zero _ := Subsingleton.elim _ _
  dist_triangle _ _ _ := show (0 : ℝ) ≤ 0 + 0 by rw [add_zero]
  toUniformSpace := inferInstance
  uniformity_dist := by
    simp (config := { contextual := true }) [principal_univ, eq_top_of_neBot (𝓤 PUnit)]

section Real

/-- Instantiate the reals as a metric space. -/
instance Real.metricSpace : MetricSpace ℝ := .ofT0PseudoMetricSpace ℝ
#align real.metric_space Real.metricSpace

end Real

section NNReal

instance : MetricSpace ℝ≥0 :=
  Subtype.metricSpace

end NNReal

instance [MetricSpace β] : MetricSpace (ULift β) :=
  MetricSpace.induced ULift.down ULift.down_injective ‹_›

section Prod

instance Prod.metricSpaceMax [MetricSpace β] : MetricSpace (γ × β) := .ofT0PseudoMetricSpace _
#align prod.metric_space_max Prod.metricSpaceMax

end Prod

section Pi

open Finset

variable {π : β → Type*} [Fintype β] [∀ b, MetricSpace (π b)]

/-- A finite product of metric spaces is a metric space, with the sup distance. -/
instance metricSpacePi : MetricSpace (∀ b, π b) := .ofT0PseudoMetricSpace _
#align metric_space_pi metricSpacePi

end Pi

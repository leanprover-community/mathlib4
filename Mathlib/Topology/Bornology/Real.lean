/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.Order.Bornology

/-!
# The reals are equipped with their order bornology

This file contains results related to the order bornology on (non-negative) real numbers.
We prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology.
-/

assert_not_exists IsTopologicalRing UniformContinuousConstSMul UniformOnFun

open Metric Set

instance Real.instIsOrderBornology : IsOrderBornology ℝ :=
  .of_isCompactIcc 0 (by simp [closedBall_eq_Icc]) (by simp [closedBall_eq_Icc])

namespace NNReal

instance : OrderTopology ℝ≥0 :=
  orderTopology_of_ordConnected (t := Ici 0)

instance : IsOrderBornology ℝ≥0 := .of_isCompactIcc 0 (by simp) fun r ↦ by
  obtain hr | hr := le_or_gt 0 r <;> simp [closedBall_zero_eq_Icc, *]

end NNReal

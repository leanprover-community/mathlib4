/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Order.Bornology
public import Mathlib.Topology.MetricSpace.Pseudo.Constructions
public import Mathlib.Topology.Order.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Order.Interval.Set.OrdConnected
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
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# The reals are equipped with their order bornology

This file contains results related to the order bornology on (non-negative) real numbers.
We prove that `ℝ` and `ℝ≥0` are equipped with the order topology and bornology.
-/

@[expose] public section

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

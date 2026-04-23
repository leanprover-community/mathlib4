/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Alex J. Best
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Module.Field
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.EReal.Inv
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Floor
import Mathlib.Init
import Mathlib.Tactic.Bound.Init
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.SetLike
import Mathlib.Tactic.Translate.ToAdditive
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.MetricSpace.Bounded

/-!
# Pointwise set operations on `MeasurableSet`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `MeasurableSet.mul` etc.
-/

public section


open Pointwise

open Set

@[to_additive]
theorem MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α]
    [MeasurableSpace α] [MeasurableConstSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  exact measurable_const_smul _ hs

theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type*} [GroupWithZero G₀] [MulAction G₀ α]
    [MeasurableSpace α] [MeasurableConstSMul G₀ α] {s : Set α}
    (hs : MeasurableSet s) {a : G₀} (ha : a ≠ 0) : MeasurableSet (a • s) := by
  rw [← preimage_smul_inv₀ ha]
  exact measurable_const_smul _ hs

theorem MeasurableSet.const_smul₀ {G₀ α : Type*} [GroupWithZero G₀] [Zero α]
    [MulActionWithZero G₀ α] [MeasurableSpace α] [MeasurableConstSMul G₀ α]
    [MeasurableSingletonClass α] {s : Set α} (hs : MeasurableSet s) (a : G₀) :
    MeasurableSet (a • s) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  exacts [(subsingleton_zero_smul_set s).measurableSet, hs.const_smul_of_ne_zero ha]

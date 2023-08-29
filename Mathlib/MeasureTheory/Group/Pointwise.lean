/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov, Alex J. Best
-/
import Mathlib.MeasureTheory.Group.Arithmetic

#align_import measure_theory.group.pointwise from "leanprover-community/mathlib"@"66f7114a1d5cba41c47d417a034bbb2e96cf564a"

/-!
# Pointwise set operations on `MeasurableSet`s

In this file we prove several versions of the following fact: if `s` is a measurable set, then so is
`a • s`. Note that the pointwise product of two measurable sets need not be measurable, so there is
no `MeasurableSet.mul` etc.
-/


open Pointwise

open Set

@[to_additive]
theorem MeasurableSet.const_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace G]
    [MeasurableSpace α] [MeasurableSMul G α] {s : Set α} (hs : MeasurableSet s) (a : G) :
    MeasurableSet (a • s) := by
  rw [← preimage_smul_inv]
  -- ⊢ MeasurableSet ((fun x => a⁻¹ • x) ⁻¹' s)
  exact measurable_const_smul _ hs
  -- 🎉 no goals
#align measurable_set.const_smul MeasurableSet.const_smul
#align measurable_set.const_vadd MeasurableSet.const_vadd

theorem MeasurableSet.const_smul_of_ne_zero {G₀ α : Type*} [GroupWithZero G₀] [MulAction G₀ α]
    [MeasurableSpace G₀] [MeasurableSpace α] [MeasurableSMul G₀ α] {s : Set α}
    (hs : MeasurableSet s) {a : G₀} (ha : a ≠ 0) : MeasurableSet (a • s) := by
  rw [← preimage_smul_inv₀ ha]
  -- ⊢ MeasurableSet ((fun x => a⁻¹ • x) ⁻¹' s)
  exact measurable_const_smul _ hs
  -- 🎉 no goals
#align measurable_set.const_smul_of_ne_zero MeasurableSet.const_smul_of_ne_zero

theorem MeasurableSet.const_smul₀ {G₀ α : Type*} [GroupWithZero G₀] [Zero α]
    [MulActionWithZero G₀ α] [MeasurableSpace G₀] [MeasurableSpace α] [MeasurableSMul G₀ α]
    [MeasurableSingletonClass α] {s : Set α} (hs : MeasurableSet s) (a : G₀) :
    MeasurableSet (a • s) := by
  rcases eq_or_ne a 0 with (rfl | ha)
  -- ⊢ MeasurableSet (0 • s)
  exacts [(subsingleton_zero_smul_set s).measurableSet, hs.const_smul_of_ne_zero ha]
  -- 🎉 no goals
#align measurable_set.const_smul₀ MeasurableSet.const_smul₀

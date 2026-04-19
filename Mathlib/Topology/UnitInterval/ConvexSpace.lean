/-
Copyright (c) 2025 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.ConvexSpace
public import Mathlib.Topology.UnitInterval

/-!
# Convex combinations parameterized by the unit interval

This file provides the definition `unitInterval.convexCombo` for computing convex combinations
in any convex space, parameterized by a point in the unit interval.

## Main definitions

* `unitInterval.convexCombo`: Given `t : unitInterval` and `x y : M` in a convex space,
  returns the convex combination `(1 - t) * x + t * y`.

## Main results

* `unitInterval.convexCombo_zero`: `convexCombo 0 x y = x`
* `unitInterval.convexCombo_one`: `convexCombo 1 x y = y`
* `unitInterval.convexCombo_same`: `convexCombo t x x = x`

-/

@[expose] public section

open scoped unitInterval

namespace unitInterval

variable {M : Type*} [ConvexSpace ℝ M]

/-- Convex combination in a convex space, parameterized by a point in the unit interval.
`convexCombo t x y` computes `(1 - t) * x + t * y`. -/
noncomputable def convexCombo (t : unitInterval) (x y : M) : M :=
  convexComboPair (1 - (t : ℝ)) (t : ℝ) (by nlinarith [t.2.1, t.2.2]) t.2.1 (by ring) x y

@[simp]
theorem convexCombo_zero (x y : M) : convexCombo 0 x y = x := by
  simp [convexCombo]

@[simp]
theorem convexCombo_one (x y : M) : convexCombo 1 x y = y := by
  simp [convexCombo]

@[simp]
theorem convexCombo_same (t : unitInterval) (x : M) : convexCombo t x x = x := by
  unfold convexCombo
  exact convexComboPair_same _ _ _

end unitInterval

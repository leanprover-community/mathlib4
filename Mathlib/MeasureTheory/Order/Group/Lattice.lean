/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability results on groups with a lattice structure.

## Tags

measurable function, group, lattice operation
-/

variable {R : Type*} [Lattice R] [Group R] [MeasurableSpace R] [MeasurableSup₂ R]
  [MeasurableInv R]

@[to_additive (attr := measurability)]
theorem measurable_mabs : Measurable fun x : R ↦ mabs x :=
  Measurable.sup measurable_id' measurable_inv

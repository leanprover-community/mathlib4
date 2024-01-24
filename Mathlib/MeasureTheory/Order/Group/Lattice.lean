/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
import Mathlib.Algebra.Order.Group.PosPart
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Order.Lattice


/-!
# Measurability results on groups with a lattice structure.

## Tags

measurable function, group, lattice operation
-/

variable {R S : Type*} [Lattice R] [Group R] [MeasurableSpace R] [MeasurableSup₂ R]
  [Lattice S] [Group S] [MeasurableSpace S] {f : S → R} (hf : Measurable f)

@[to_additive (attr := measurability)]
theorem measurable_oneLePart : Measurable fun x : R ↦ oneLePart x :=
  Measurable.sup measurable_id' measurable_const

@[to_additive (attr := measurability)]
theorem measurable.oneLePart  : Measurable fun x ↦ oneLePart (f x) :=
  Measurable.comp measurable_oneLePart hf

variable [MeasurableInv R]

@[to_additive (attr := measurability)]
theorem measurable_mabs : Measurable fun x : R ↦ mabs x :=
  Measurable.sup measurable_id' measurable_inv

@[to_additive (attr := measurability)]
theorem Measurable.mabs : Measurable fun x ↦ mabs (f x) :=
  Measurable.comp measurable_mabs hf

@[to_additive (attr := measurability)]
theorem measurable_leOnePart : Measurable fun x : R ↦ leOnePart x :=
  Measurable.sup measurable_inv measurable_const

@[to_additive (attr := measurability)]
theorem Measurable.leOnePart : Measurable fun x ↦ leOnePart (f x) :=
  Measurable.comp measurable_leOnePart hf

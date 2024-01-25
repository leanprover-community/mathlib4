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

variable {α β : Type*} [Lattice α] [Group α] [MeasurableSpace α]
  [MeasurableSpace β] {f : β → α} (hf : Measurable f)

variable [MeasurableSup α]

@[to_additive (attr := measurability)]
theorem measurable_oneLePart : Measurable fun x : α ↦ oneLePart x :=
  measurable_sup_const _

@[to_additive (attr := measurability)]
protected theorem Measurable.oneLePart : Measurable fun x ↦ oneLePart (f x) :=
  measurable_oneLePart.comp hf

variable [MeasurableInv α]

@[to_additive (attr := measurability)]
theorem measurable_leOnePart : Measurable fun x : α ↦ leOnePart x :=
  (measurable_sup_const _).comp measurable_inv

@[to_additive (attr := measurability)]
protected theorem Measurable.leOnePart : Measurable fun x ↦ leOnePart (f x) :=
  measurable_leOnePart.comp  hf

variable [MeasurableSup₂ α]

@[to_additive (attr := measurability)]
theorem measurable_mabs : Measurable fun x : α ↦ mabs x :=
  measurable_id'.sup measurable_inv

@[to_additive (attr := measurability)]
theorem Measurable.mabs : Measurable fun x ↦ mabs (f x) :=
  measurable_mabs.comp  hf

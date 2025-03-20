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
  [MeasurableSpace β] {f : β → α}

@[to_additive (attr := measurability)]
theorem measurable_oneLePart [MeasurableSup α] : Measurable (oneLePart : α → α) :=
  measurable_sup_const _

@[to_additive (attr := measurability)]
protected theorem Measurable.oneLePart [MeasurableSup α] (hf : Measurable f) :
    Measurable fun x ↦ oneLePart (f x) :=
  measurable_oneLePart.comp hf

variable [MeasurableInv α]

@[to_additive (attr := measurability)]
theorem measurable_leOnePart [MeasurableSup α] : Measurable (leOnePart : α → α) :=
  (measurable_sup_const _).comp measurable_inv

@[to_additive (attr := measurability)]
protected theorem Measurable.leOnePart [MeasurableSup α] (hf : Measurable f) :
    Measurable fun x ↦ leOnePart (f x) :=
  measurable_leOnePart.comp hf

variable [MeasurableSup₂ α]

@[to_additive (attr := measurability)]
theorem measurable_mabs : Measurable (mabs : α → α) :=
  measurable_id'.sup measurable_inv

@[to_additive (attr := measurability, fun_prop)]
protected theorem Measurable.mabs (hf : Measurable f) : Measurable fun x ↦ mabs (f x) :=
  measurable_mabs.comp hf

@[to_additive (attr := measurability, fun_prop)]
protected theorem AEMeasurable.mabs {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ mabs (f x)) μ :=
  measurable_mabs.comp_aemeasurable hf

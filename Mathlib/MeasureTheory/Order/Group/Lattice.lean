/-
Copyright (c) 2024 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/
module

public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Order.Lattice

/-!
# Measurability results on groups with a lattice structure.

## Tags

measurable function, group, lattice operation
-/

public section

variable {α β : Type*} [Lattice α] [MeasurableSpace α] [MeasurableSpace β] {f : β → α}

section DivInvMonoid

variable [DivInvMonoid α] [MeasurableSup α]

@[to_additive]
theorem measurable_oneLePart : Measurable (oneLePart : α → α) :=
  measurable_sup_const _

@[to_fun (attr := to_additive (attr := fun_prop))]
protected theorem Measurable.oneLePart (hf : Measurable f) :
    Measurable f⁺ᵐ := measurable_oneLePart.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
protected theorem AEMeasurable.oneLePart {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable f⁺ᵐ μ := hf.sup_const 1

variable [MeasurableInv α]

@[to_additive]
theorem measurable_leOnePart : Measurable (leOnePart : α → α) :=
  (measurable_sup_const _).comp measurable_inv

@[to_fun (attr := to_additive (attr := fun_prop))]
protected theorem Measurable.leOnePart (hf : Measurable f) :
    Measurable f⁻ᵐ := measurable_leOnePart.comp hf

@[to_fun (attr := to_additive (attr := fun_prop))]
protected theorem AEMeasurable.leOnePart {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable f⁻ᵐ μ := hf.inv.sup_const 1

end DivInvMonoid

section Group

variable [Group α] [MeasurableInv α] [MeasurableSup₂ α]

@[to_additive]
theorem measurable_mabs : Measurable (mabs : α → α) :=
  measurable_id'.sup measurable_inv

@[to_additive (attr := fun_prop)]
protected theorem Measurable.mabs (hf : Measurable f) : Measurable fun x ↦ mabs (f x) :=
  measurable_mabs.comp hf

@[to_additive (attr := fun_prop)]
protected theorem AEMeasurable.mabs {μ : MeasureTheory.Measure β} (hf : AEMeasurable f μ) :
    AEMeasurable (fun x ↦ mabs (f x)) μ :=
  measurable_mabs.comp_aemeasurable hf

end Group

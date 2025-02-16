/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.GroupTheory.GroupAction.IterateAct
import Mathlib.Data.Rat.Init
import Mathlib.Data.ZMod.Defs

/-!
# Measurable-space typeclass instances

This file provides measurable-space instances for a selection of standard countable types,
in each case defining the Σ-algebra to be `⊤` (the discrete measurable-space structure).
-/

instance Empty.instMeasurableSpace : MeasurableSpace Empty := ⊤

instance PUnit.instMeasurableSpace : MeasurableSpace PUnit := ⊤

instance Bool.instMeasurableSpace : MeasurableSpace Bool := ⊤

instance Prop.instMeasurableSpace : MeasurableSpace Prop := ⊤

instance Nat.instMeasurableSpace : MeasurableSpace ℕ := ⊤

instance ENat.instMeasurableSpace : MeasurableSpace ℕ∞ := ⊤

instance Fin.instMeasurableSpace (n : ℕ) : MeasurableSpace (Fin n) := ⊤

instance ZMod.instMeasurableSpace (n : ℕ) : MeasurableSpace (ZMod n) := ⊤

instance Int.instMeasurableSpace : MeasurableSpace ℤ := ⊤

instance Rat.instMeasurableSpace : MeasurableSpace ℚ := ⊤

@[to_additive]
instance IterateMulAct.instMeasurableSpace {α : Type*} {f : α → α} :
    MeasurableSpace (IterateMulAct f) := ⊤

@[to_additive]
instance IterateMulAct.instDiscreteMeasurableSpace {α : Type*} {f : α → α} :
    DiscreteMeasurableSpace (IterateMulAct f) := inferInstance

instance (priority := 100) Subsingleton.measurableSingletonClass
    {α} [MeasurableSpace α] [Subsingleton α] : MeasurableSingletonClass α := by
  refine ⟨fun i => ?_⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall, eq_iff_true_of_subsingleton]

instance Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩

instance Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ => trivial⟩

instance Nat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ := ⟨fun _ => trivial⟩

instance ENat.instDiscreteMeasurableSpace : DiscreteMeasurableSpace ℕ∞ := ⟨fun _ ↦ trivial⟩

instance ENat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ∞ := inferInstance

instance Fin.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩

instance ZMod.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (ZMod n) :=
  ⟨fun _ => trivial⟩

instance Int.instMeasurableSingletonClass : MeasurableSingletonClass ℤ := ⟨fun _ => trivial⟩

instance Rat.instMeasurableSingletonClass : MeasurableSingletonClass ℚ := ⟨fun _ => trivial⟩

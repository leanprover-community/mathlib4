/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Data.Rat.Init

#align_import measure_theory.measurable_space from "leanprover-community/mathlib"@"001ffdc42920050657fd45bd2b8bfbec8eaaeb29"

/-!
# Measurable-space typeclass instances

This file provides measurable-space instances for a selection of standard countable types,
in each case defining the Σ-algebra to be `⊤` (the discrete measurable-space structure).
-/

instance Empty.instMeasurableSpace : MeasurableSpace Empty := ⊤
#align empty.measurable_space Empty.instMeasurableSpace

instance PUnit.instMeasurableSpace : MeasurableSpace PUnit := ⊤
#align punit.measurable_space PUnit.instMeasurableSpace

instance Bool.instMeasurableSpace : MeasurableSpace Bool := ⊤
#align bool.measurable_space Bool.instMeasurableSpace

instance Prop.instMeasurableSpace : MeasurableSpace Prop := ⊤
#align Prop.measurable_space Prop.instMeasurableSpace

instance Nat.instMeasurableSpace : MeasurableSpace ℕ := ⊤
#align nat.measurable_space Nat.instMeasurableSpace

instance Fin.instMeasurableSpace (n : ℕ) : MeasurableSpace (Fin n) := ⊤

instance Int.instMeasurableSpace : MeasurableSpace ℤ := ⊤
#align int.measurable_space Int.instMeasurableSpace

instance Rat.instMeasurableSpace : MeasurableSpace ℚ := ⊤
#align rat.measurable_space Rat.instMeasurableSpace

instance Subsingleton.measurableSingletonClass {α} [MeasurableSpace α] [Subsingleton α] :
    MeasurableSingletonClass α := by
  refine ⟨fun i => ?_⟩
  convert MeasurableSet.univ
  simp [Set.eq_univ_iff_forall, eq_iff_true_of_subsingleton]
#noalign empty.measurable_singleton_class
#noalign punit.measurable_singleton_class

instance Bool.instMeasurableSingletonClass : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
#align bool.measurable_singleton_class Bool.instMeasurableSingletonClass

instance Prop.instMeasurableSingletonClass : MeasurableSingletonClass Prop := ⟨fun _ => trivial⟩
#align Prop.measurable_singleton_class Prop.instMeasurableSingletonClass

instance Nat.instMeasurableSingletonClass : MeasurableSingletonClass ℕ := ⟨fun _ => trivial⟩
#align nat.measurable_singleton_class Nat.instMeasurableSingletonClass

instance Fin.instMeasurableSingletonClass (n : ℕ) : MeasurableSingletonClass (Fin n) :=
  ⟨fun _ => trivial⟩

instance Int.instMeasurableSingletonClass : MeasurableSingletonClass ℤ := ⟨fun _ => trivial⟩
#align int.measurable_singleton_class Int.instMeasurableSingletonClass

instance Rat.instMeasurableSingletonClass : MeasurableSingletonClass ℚ := ⟨fun _ => trivial⟩
#align rat.measurable_singleton_class Rat.instMeasurableSingletonClass

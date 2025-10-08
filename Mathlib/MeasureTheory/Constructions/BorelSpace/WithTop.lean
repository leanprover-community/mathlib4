/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Topology.Order.WithTop

/-!
# Borel measurable space on `WithTop`

## Main definitions

* `FooBar`

## Main statements

* `fooBar_unique`

-/


namespace WithTop

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

instance : MeasurableSpace (WithTop ι) := borel _

instance : BorelSpace (WithTop ι) := ⟨rfl⟩

variable [MeasurableSpace ι] [BorelSpace ι]

/-- Measurable equivalence between the non-top elements of `WithTop ι` and `ι`. -/
noncomputable
def MeasurableEquiv.withTopEquiv [Nonempty ι] : { r : WithTop ι | r ≠ ⊤ } ≃ᵐ ι :=
  (WithTop.neTopHomeomorph ι).toMeasurableEquiv

lemma measurable_of_measurable_comp_coe {α : Type*} {mα : MeasurableSpace α}
    {f : WithTop ι → α} (h : Measurable fun p : ι ↦ f p) :
    Measurable f := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact Subsingleton.measurable
  · exact measurable_of_measurable_on_compl_singleton ⊤
      (MeasurableEquiv.withTopEquiv.symm.measurable_comp_iff.1 h)

lemma measurable_untopA [Nonempty ι] : Measurable (WithTop.untopA (ι := ι)) :=
  measurable_of_measurable_comp_coe measurable_id

lemma measurable_coe :
    Measurable (fun x : ι ↦ (x : WithTop ι)) := continuous_coe.measurable

@[fun_prop]
lemma _root_.Measurable.withTop_coe {α} {mα : MeasurableSpace α} [SecondCountableTopology ι]
    {f : α → ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x : WithTop ι)) := by
  refine measurable_of_Iic fun i ↦ ?_
  cases i with
  | top => simp
  | coe i =>
    have : ((fun x ↦ ↑(f x)) ⁻¹' Set.Iic (i : WithTop ι)) = (f ⁻¹' Set.Iic i) := by ext; simp
    rw [this]
    exact hf measurableSet_Iic

@[fun_prop]
lemma _root_.Measurable.untopA {α} {mα : MeasurableSpace α} [Nonempty ι]
    {f : α → WithTop ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x).untopA) := measurable_untopA.comp hf

/-- Measurable equivalence between `WithTop ι` and `ι ⊕ Unit`. -/
def measurableEquivSum : WithTop ι ≃ᵐ ι ⊕ Unit :=
  { Equiv.optionEquivSumPUnit ι with
    measurable_toFun := measurable_of_measurable_comp_coe measurable_inl
    measurable_invFun := measurable_fun_sum measurable_coe (@measurable_const _ Unit _ _ ⊤) }

end WithTop

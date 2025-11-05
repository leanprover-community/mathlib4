/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.Order.WithTop

/-!
# Borel measurable space on `WithTop`

For `ι` a linear order with the order topology, we define the Borel measurable space on `WithTop ι`.
We then prove that the natural inclusion `ι → WithTop ι` is measurable, and that the function
`WithTop.untopA : WithTop ι → ι` (which sends `⊤` to an arbitrary element of `ι`) is measurable.

## Main statements

* `measurable_of_measurable_comp_coe`: if `f : WithTop ι → α` is such that `f ∘ coe` is measurable,
  then `f` is measurable.
* `Measurable.withTop_coe`: the function `fun x : ι ↦ (x : WithTop ι)` is measurable.
* `Measurable.untopD`: for `d : ι`, the function `WithTop.untopD d : WithTop ι → ι` is measurable.
* `Measurable.untopA`: the function `WithTop.untopA : WithTop ι → ι` is measurable.

-/


namespace WithTop

variable {ι : Type*} [LinearOrder ι] [TopologicalSpace ι] [OrderTopology ι]

instance : MeasurableSpace (WithTop ι) := borel _

instance : BorelSpace (WithTop ι) := ⟨rfl⟩

variable [MeasurableSpace ι] [BorelSpace ι]

/-- Measurable equivalence between the non-top elements of `WithTop ι` and `ι`. -/
noncomputable
def MeasurableEquiv.neTopEquiv : { r : WithTop ι | r ≠ ⊤ } ≃ᵐ ι :=
  (WithTop.neTopHomeomorph ι).toMeasurableEquiv

lemma measurable_of_measurable_comp_coe {α : Type*} {mα : MeasurableSpace α}
    {f : WithTop ι → α} (h : Measurable fun p : ι ↦ f p) :
    Measurable f :=
  measurable_of_measurable_on_compl_singleton ⊤
    (MeasurableEquiv.neTopEquiv.symm.measurable_comp_iff.1 h)

lemma measurable_untopD (d : ι) : Measurable (untopD d) :=
  measurable_of_measurable_comp_coe measurable_id

lemma measurable_untopA [Nonempty ι] : Measurable (WithTop.untopA (α := ι)) :=
  measurable_untopD _

lemma measurable_coe : Measurable (fun x : ι ↦ (x : WithTop ι)) := continuous_coe.measurable

@[fun_prop]
lemma _root_.Measurable.withTop_coe {α} {mα : MeasurableSpace α} {f : α → ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x : WithTop ι)) :=
  measurable_coe.comp hf

@[fun_prop]
lemma _root_.Measurable.untopD {α} {mα : MeasurableSpace α} (d : ι)
    {f : α → WithTop ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x).untopD d) := (measurable_untopD d).comp hf

@[fun_prop]
lemma _root_.Measurable.untopA {α} {mα : MeasurableSpace α} [Nonempty ι]
    {f : α → WithTop ι} (hf : Measurable f) :
    Measurable (fun x ↦ (f x).untopA) := hf.untopD _

/-- Measurable equivalence between `WithTop ι` and `ι ⊕ Unit`. -/
def measurableEquivSum : WithTop ι ≃ᵐ ι ⊕ Unit :=
  { Equiv.optionEquivSumPUnit ι with
    measurable_toFun := measurable_of_measurable_comp_coe measurable_inl
    measurable_invFun := measurable_fun_sum measurable_coe (@measurable_const _ Unit _ _ ⊤) }

end WithTop

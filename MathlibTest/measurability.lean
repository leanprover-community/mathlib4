/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lemmas


open MeasureTheory TopologicalSpace

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {f g : α → β} {s₁ s₂ : Set α} {t₁ t₂ : Set β} {μ ν : MeasureTheory.Measure α}

set_option linter.unusedVariables false

-- Test the use of assumption

example (hf : Measurable f) : Measurable f := by measurability

-- Test that intro does not unfold `Measurable`

example : Measurable f → Measurable f := by measurability

-- Test the use of apply_assumption to get (h i) from a hypothesis (h : ∀ i, ...).

example {F : ℕ → α → β} (hF : ∀ i, Measurable (F i)) : Measurable (F 0) := by measurability

example {ι} [Encodable ι] {S₁ S₂ : ι → Set α} (hS₁ : ∀ i, MeasurableSet (S₁ i))
    (hS₂ : ∀ i, MeasurableSet (S₂ i)) : MeasurableSet (⋃ i, (S₁ i) ∪ (S₂ i)) := by measurability

-- Tests on sets

example (hs₁ : MeasurableSet s₁) (hs₂ : MeasurableSet s₂) : MeasurableSet (s₁ ∪ s₁) := by
  measurability

example {ι} [Encodable ι] {S : ι → Set α} (hs : ∀ i, MeasurableSet (S i)) :
    MeasurableSet (⋃ i, S i) := by measurability

example (hf : Measurable f) (hs₁ : MeasurableSet s₁) (ht₂ : MeasurableSet t₂) :
    MeasurableSet ((f ⁻¹' t₂) ∩ s₁) := by measurability

-- Strong measurability
section strong_measurability

variable [TopologicalSpace β] [PseudoMetrizableSpace β] [BorelSpace β]

-- Test the use of apply_assumption to get (h i) from a hypothesis (h : ∀ i, ...).

example {F : ℕ → α → β} (hF : ∀ i, StronglyMeasurable (F i)) : Measurable (F 0) := by
  measurability

example [Zero β] {F : ℕ → α → β} (hF : ∀ i, AEFinStronglyMeasurable (F i) μ) :
    AEMeasurable (F 0) μ := by measurability

example {ι} [Encodable ι] {S₁ S₂ : ι → Set α} (hS₁ : ∀ i, MeasurableSet (S₁ i))
    (hS₂ : ∀ i, MeasurableSet (S₂ i)) : MeasurableSet (⋃ i, (S₁ i) ∪ (S₂ i)) := by measurability

end strong_measurability

/-- `ℝ` is a good test case because it verifies many assumptions, hence many lemmas apply and we
are more likely to detect a bad lemma. In a previous version of the tactic, `measurability` got
stuck trying to apply `Set.Finite.MeasurableSet` here. -/
example {a b : ℝ} : MeasurableSet (Set.Icc a b) := by measurability

-- Tests on functions

example [Mul β] [MeasurableMul₂ β] (hf : Measurable f) (c : β) :
    Measurable (fun x => c * f x) := by measurability  -- uses const_mul, not mul

example [Add β] [MeasurableAdd₂ β] (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x + g x) := by measurability

example [Add β] [MeasurableAdd₂ β] (hf : Measurable f) (hg : AEMeasurable g μ) :
    AEMeasurable (fun x => f x + g x) μ := by measurability

example [Div β] [MeasurableDiv₂ β] (hf : Measurable f) (hg : Measurable g)
    (ht : MeasurableSet t₂) : MeasurableSet ((fun x => f x / g x) ⁻¹' t₂) := by measurability

example [AddCommMonoid β] [MeasurableAdd₂ β] {s : Finset ℕ} {F : ℕ → α → β}
    (hF : ∀ i, Measurable (F i)) : Measurable (∑ i ∈ s, (fun x => F (i+1) x + F i x)) := by
  fun_prop

example [AddCommMonoid β] [MeasurableAdd₂ β] {s : Finset ℕ} {F : ℕ → α → β}
    (hF : ∀ i, AEMeasurable (F i) μ) : AEMeasurable (∑ i ∈ s, (fun x => F (i+1) x + F i x)) μ := by
  measurability

-- even with many assumptions, the tactic is not trapped by a bad lemma
example [TopologicalSpace α] [BorelSpace α] [NormedAddCommGroup β] [BorelSpace β]
    [MeasurableAdd₂ β] [MeasurableSub₂ β] {s : Finset ℕ} {F : ℕ → α → β}
    (hF : ∀ i, Measurable (F i)) : AEMeasurable (∑ i ∈ s, (fun x => F (i+1) x - F i x)) μ := by
  measurability

open scoped RealInnerProductSpace

example : Measurable (fun x : ℝ => Real.exp (2 * ⟪3, x⟫)) := by measurability

example : StronglyMeasurable (fun x : ℝ => Real.exp (2 * ⟪3, x⟫)) := by measurability

example {γ : MeasureTheory.Measure ℝ} :
  AEMeasurable (fun x : ℝ => Real.exp (2 * ⟪3, x⟫)) γ := by measurability

example {γ : MeasureTheory.Measure ℝ} :
  AEStronglyMeasurable (fun x : ℝ => Real.exp (2 * ⟪3, x⟫)) γ := by measurability

example {γ : MeasureTheory.Measure ℝ} [SigmaFinite γ] :
  FinStronglyMeasurable (fun x : ℝ => Real.exp (2 * ⟪3, x⟫)) γ := by measurability

example {γ : MeasureTheory.Measure ℝ} [SigmaFinite γ] :
  AEFinStronglyMeasurable (fun x : ℝ => Real.exp (2 * ⟪3, x⟫)) γ := by measurability

/-- An older version of the tactic failed in the presence of a negated hypothesis due to an
internal call to `apply_assumption`. -/
example {ι : Type _} (i k : ι) (hik : i ≠ k) : Measurable (id : α → α) := by measurability

--This search problem loops (StronglyMeasurable -> Measurable -> StronglyMeasurable) but fails
--quickly nevertheless.
--example (f : ℝ → ℝ) : StronglyMeasurable f := by measurability

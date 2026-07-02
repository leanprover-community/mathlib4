/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# Aux lemmas: move them elsewhere

-/

@[expose] public section

open scoped ENNReal

noncomputable
instance : ENorm EReal where
  enorm x := (max x 0).toENNReal + (max (-x) 0).toENNReal

section PosNeg

open MeasureTheory

variable {α β : Type*} {mα : MeasurableSpace α} {μ : Measure α} [SubNegMonoid β] [Lattice β]

@[simp]
lemma posPartFun_nonneg (f : α → β) (x : α) : 0 ≤ f⁺ x := posPart_nonneg f x

@[simp]
lemma negPartFun_nonneg (f : α → β) (x : α) : 0 ≤ f⁻ x := negPart_nonneg f x

lemma posPartFun_sub_negPartFun (f : α → EReal) (x : α) : f⁺ x - f⁻ x = f x := by
  rcases le_total 0 (f x) with h | h <;> simp [posPart_def, negPart_def, h]

lemma posPartFun_eq_zero_or_negPartFun_eq_zero (f : α → EReal) (x : α) :
    f⁺ x = 0 ∨ f⁻ x = 0 := by
  rcases le_total 0 (f x) with h | h <;> simp [posPart_def, negPart_def, h]

variable {f : α → EReal}

@[fun_prop]
lemma Measurable.posPartFun (hf : Measurable f) : Measurable (fun x ↦ f⁺ x) := by
  simp only [posPart_def]
  fun_prop

@[fun_prop]
lemma Measurable.negPartFun (hf : Measurable f) : Measurable (fun x ↦ f⁻ x) := by
  simp only [negPart_def]
  fun_prop

@[fun_prop]
lemma AEMeasurable.posPartFun (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ f⁺ x) μ := by
  simp only [posPart_def]
  fun_prop

@[fun_prop]
lemma AEMeasurable.negPartFun (hf : AEMeasurable f μ) : AEMeasurable (fun x ↦ f⁻ x) μ := by
  simp only [negPart_def]
  fun_prop

end PosNeg

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
  enorm x := x⁺.toENNReal + x⁻.toENNReal

section PosNeg

open MeasureTheory

lemma EReal.posPart_sub_negPart (x : EReal) : x⁺ - x⁻ = x := by
  rcases le_total 0 x with h | h <;> simp [negPart_def, h]

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [DivInvMonoid β] [Lattice β] [MeasurableSup β]
  {μ : Measure α} {f : α → β}

@[to_additive (attr := fun_prop)]
lemma Measurable.oneLePart (hf : Measurable f) : Measurable f⁺ᵐ := hf.sup_const 1

@[to_additive (attr := fun_prop)]
lemma Measurable.leOnePart [MeasurableInv β] (hf : Measurable f) : Measurable f⁻ᵐ :=
  hf.inv.sup_const 1

@[to_additive (attr := fun_prop)]
lemma AEMeasurable.oneLePart (hf : AEMeasurable f μ) : AEMeasurable f⁺ᵐ μ := hf.sup_const 1

@[to_additive (attr := fun_prop)]
lemma AEMeasurable.leOnePart [MeasurableInv β] (hf : AEMeasurable f μ) : AEMeasurable f⁻ᵐ μ :=
  hf.inv.sup_const 1

end PosNeg

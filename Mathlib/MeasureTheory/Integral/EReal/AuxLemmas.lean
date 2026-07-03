/-
Copyright (c) 2025 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré, Rémy Degenne
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.MeasureTheory.Group.Arithmetic
public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.MeasureTheory.Order.Group.Lattice

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

variable {α : Type*} {mα : MeasurableSpace α}

lemma EReal.posPart_fun_sub_negPart_fun_apply (f : α → EReal) (x : α) : f⁺ x - f⁻ x = f x := by
  rcases le_total 0 (f x) with h | h <;> simp [posPart_def, negPart_def, h]

lemma EReal.posPart_fun_sub_negPart_fun (f : α → EReal) : f⁺ - f⁻ = f := by
  ext x
  simp only [Pi.sub_apply]
  exact EReal.posPart_fun_sub_negPart_fun_apply f x

lemma EReal.posPart_fun_eq_zero_or_negPart_fun_eq_zero (f : α → EReal) (x : α) :
    f⁺ x = 0 ∨ f⁻ x = 0 := by
  rcases le_total 0 (f x) with h | h <;> simp [posPart_def, negPart_def, h]

end PosNeg

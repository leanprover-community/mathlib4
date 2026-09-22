/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# Additive characters on finite fields

We construct a primitive additive character on a finite field `F` with values in `ℂ`.
This file is kept separate from `Mathlib.NumberTheory.LegendreSymbol.AddCharacter` to avoid
importing the fundamental theorem of algebra and Bochner integral into that file.
-/

namespace AddChar

section Field

variable (F : Type*) [Field F] [Finite F]

lemma ringChar_ne : ringChar ℂ ≠ ringChar F := by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

/-- A primitive additive character on the finite field `F` with values in `ℂ`. -/
public noncomputable def FiniteField.primitiveChar_to_Complex : AddChar F ℂ := by
  letI ch := primitiveChar F ℂ <| by exact ringChar_ne F
  refine MonoidHom.compAddChar ?_ ch.char
  exact (IsCyclotomicExtension.algEquiv {(ch.n : ℕ)} ℂ (CyclotomicField ch.n ℂ) ℂ).toMonoidHom

public lemma FiniteField.primitiveChar_to_Complex_isPrimitive :
    (primitiveChar_to_Complex F).IsPrimitive := by
  refine IsPrimitive.compMulHom_of_isPrimitive (PrimitiveAddChar.prim _) ?_
  let nn := (primitiveChar F ℂ <| ringChar_ne F).n
  exact (IsCyclotomicExtension.algEquiv {(nn : ℕ)} ℂ (CyclotomicField nn ℂ) ℂ).injective

end Field

end AddChar

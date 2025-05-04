/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction


open ArithmeticFunction

variable {R : Type*} [Field R]

set_option linter.unusedVariables false

example : IsMultiplicative μ := by arith_mult

example : IsMultiplicative (ζ * ζ) := by arith_mult

example {R : Type*} [Field R] (f : ArithmeticFunction R) (hf : IsMultiplicative f) :
    IsMultiplicative ((ζ : ArithmeticFunction R).pdiv f) := by arith_mult

example (f g : ArithmeticFunction R) (hf : IsMultiplicative f) :
    IsMultiplicative (prodPrimeFactors g |>.pmul f) := by arith_mult

example (n : ℕ) : IsMultiplicative <| (σ n * pow (n + 3)).ppow 2 := by arith_mult

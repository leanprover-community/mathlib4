/-
Copyright (c) 2023 Arend Mellendijk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arend Mellendijk
-/

import Mathlib.NumberTheory.ArithmeticFunction

open scoped BigOperators
open Nat ArithmeticFunction

variable {R : Type*} [Field R]

set_option linter.unusedVariables false

example : IsMultiplicative μ := by multiplicativity

example : IsMultiplicative (ζ*ζ) := by multiplicativity

example {R : Type*} [Field R] (f : ArithmeticFunction R) (hf : IsMultiplicative f) :
    IsMultiplicative ((ζ:ArithmeticFunction R).pdiv f) := by multiplicativity

example (f g : ArithmeticFunction R) (hf : IsMultiplicative f) :
    IsMultiplicative (prodPrimeFactors g |>.pmul f) := by multiplicativity

example (n : ℕ) : IsMultiplicative <| (σ n * pow (n+3)).ppow 2 := by multiplicativity

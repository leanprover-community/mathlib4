/-
Copyright (c) 2023 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/
import Mathlib.Data.Nat.Factorial.Basic

/-!
# Superfactorial

This file defines the [superfactorial](https://en.wikipedia.org/wiki/Superfactorial)
`1! * 2! * 3! * ...* n!`.

## Main declarations

* `Nat.superFactorial`: The superfactorial.
-/


namespace Nat

/-- `Nat.superFactorial n` is the superfactorial of `n`. -/
@[simp]
def superFactorial : ℕ → ℕ
  | 0 => 1
  | succ n => factorial n.succ * superFactorial n

/-- `sf` notation for superfactorial -/
scoped notation:10000 "sf" n => Nat.superFactorial n

section SuperFactorial

variable {n : ℕ}

@[simp]
theorem superFactorial_zero : (sf 0) = 1 :=
  rfl

theorem superFactorial_succ (n : ℕ) : (sf n.succ) = (n + 1)! * sf n :=
  rfl

@[simp]
theorem superFactorial_one : (sf 1) = 1 :=
  rfl

@[simp]
theorem superFactorial_two : (sf 2) = 2 :=
  rfl

end SuperFactorial

end Nat

/-
Copyright (c) 2026 Wrenna Robson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wrenna Robson
-/
module

public import Batteries.Tactic.Alias
public import Mathlib.Data.Nat.Notation
public import Init.Data.Fin.Bitwise

/-!
# Basic operations on bounded natural numbers.

This file should not depend on anything defined in Mathlib (except for notation), so that it can be
upstreamed to Batteries or the Lean standard library easily.
-/

@[expose] public section

/- We don't want to import the algebraic hierarchy in this file. -/
assert_not_exists Monoid

namespace Fin

variable {n k : ℕ}

theorem xor_assoc (a b c : Fin (2 ^ n)) : (a ^^^ b) ^^^ c = a ^^^ (b ^^^ c) := by
  grind [Fin.xor_val, Nat.xor_mod_two_pow, Nat.mod_mod]
theorem xor_comm (a b : Fin k) : a ^^^ b = b ^^^ a := by grind [Fin.xor_val]
@[simp] theorem xor_self [NeZero k] {a : Fin k} : a ^^^ a = 0 := by
  grind [Fin.xor_val, Nat.zero_mod]
@[simp] theorem xor_zero [NeZero k] {a : Fin k} : a ^^^ 0 = a := by
  grind [Fin.xor_val, Fin.val_zero, Nat.mod_eq_of_lt]

end Fin

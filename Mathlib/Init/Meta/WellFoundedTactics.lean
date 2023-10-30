/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
prelude
import Mathlib.Init.Data.Nat.Lemmas

#align_import init.meta.well_founded_tactics from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

-- Porting note: meta code used to implement well-founded recursion is not ported

theorem Nat.lt_add_of_zero_lt_left (a b : Nat) (h : 0 < b) : a < a + b :=
  show a + 0 < a + b by
    apply Nat.add_lt_add_left
    assumption
#align nat.lt_add_of_zero_lt_left Nat.lt_add_of_zero_lt_left

theorem Nat.zero_lt_one_add (a : Nat) : 0 < 1 + a :=
  suffices 0 < a + 1 by
    simp only [Nat.add_comm]
    assumption
  Nat.zero_lt_succ _
#align nat.zero_lt_one_add Nat.zero_lt_one_add

#align nat.lt_add_right Nat.lt_add_right

theorem Nat.lt_add_left (a b c : Nat) : a < b → a < c + b := fun h =>
  lt_of_lt_of_le h (Nat.le_add_left _ _)
#align nat.lt_add_left Nat.lt_add_left

/-
The remainder of the original Lean 3 source module is subsumed by Lean 4 core.
-/

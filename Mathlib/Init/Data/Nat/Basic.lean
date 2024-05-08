/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
import Mathlib.Init.ZeroOne
import Mathlib.Init.Data.Nat.Notation
import Mathlib.Util.CompileInductive

namespace Nat

set_option linter.deprecated false

theorem add_one_pos (n : ℕ) : 0 < n + 1 := succ_pos n

protected theorem bit0_succ_eq (n : ℕ) : bit0 (succ n) = succ (succ (bit0 n)) :=
  show succ (succ n + n) = succ (succ (n + n)) from congrArg succ (succ_add n n)
#align nat.bit0_succ_eq Nat.bit0_succ_eq

protected theorem zero_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 0 < bit0 n
  | 0, h => absurd rfl h
  | succ n, _ =>
    calc
      0 < succ (succ (bit0 n)) := zero_lt_succ _
      _ = bit0 (succ n) := (Nat.bit0_succ_eq n).symm
#align nat.zero_lt_bit0 Nat.zero_lt_bit0

protected theorem zero_lt_bit1 (n : Nat) : 0 < bit1 n :=
  zero_lt_succ _
#align nat.zero_lt_bit1 Nat.zero_lt_bit1

protected theorem bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → bit0 n ≠ 0
  | 0, h => absurd rfl h
  | n + 1, _ =>
    suffices n + 1 + (n + 1) ≠ 0 from this
    suffices succ (n + 1 + n) ≠ 0 from this
    fun h => Nat.noConfusion h
#align nat.bit0_ne_zero Nat.bit0_ne_zero

protected theorem bit1_ne_zero (n : ℕ) : bit1 n ≠ 0 :=
  show succ (n + n) ≠ 0 from fun h => Nat.noConfusion h
#align nat.bit1_ne_zero Nat.bit1_ne_zero

end Nat

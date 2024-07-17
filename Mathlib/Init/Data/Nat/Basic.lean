/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura
-/
import Mathlib.Data.Nat.Notation
import Mathlib.Mathport.Rename
import Mathlib.Util.CompileInductive

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.
-/

namespace Nat

set_option linter.deprecated false

protected theorem bit0_succ_eq (n : ℕ) : 2 * (succ n) = succ (succ (2 * n)) := by
  omega
#noalign nat.bit0_succ_eq

protected theorem zero_lt_bit0 : ∀ {n : Nat}, n ≠ 0 → 0 < 2 * n := by
  omega
#align nat.zero_lt_bit0 Nat.zero_lt_bit0

protected theorem zero_lt_bit1 (n : Nat) : 0 < 2 * n + 1 :=
  zero_lt_succ _
#align nat.zero_lt_bit1 Nat.zero_lt_bit1

protected theorem bit0_ne_zero : ∀ {n : ℕ}, n ≠ 0 → 2 * n ≠ 0 := by
  omega
#align nat.bit0_ne_zero Nat.bit0_ne_zero

protected theorem bit1_ne_zero (n : ℕ) : 2 * n + 1 ≠ 0 := by
  omega
#align nat.bit1_ne_zero Nat.bit1_ne_zero

end Nat

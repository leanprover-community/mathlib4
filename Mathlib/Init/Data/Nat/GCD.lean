/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Mario Carneiro

-/

import Batteries.Data.Nat.Gcd
import Mathlib.Data.Nat.Notation
import Mathlib.Mathport.Rename

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Definitions and properties of gcd, lcm, and coprime
-/


open WellFounded

namespace Nat

/-! gcd -/

theorem gcd_def (x y : ℕ) : gcd x y = if x = 0 then y else gcd (y % x) x := by
  cases x <;> simp [Nat.gcd_succ]

end Nat

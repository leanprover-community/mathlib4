/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Order.BoundedOrder

/-!
# The natural numbers form a linear order

This file contains the linear order instance on the natural numbers.

See note [foundational algebra order theory].

## TODO

Move the `LinearOrder ℕ` instance here (#13092).
-/

namespace Nat

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le
#align nat.order_bot Nat.instOrderBot

/-! ### Miscellaneous lemmas -/

-- We want to use this lemma earlier than the lemma simp can prove it with
@[simp, nolint simpNF] protected lemma bot_eq_zero : ⊥ = 0 := rfl

end Nat

/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Data.Nat.Find
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Order.Bounds.Defs

/-!
# The natural numbers form a linear order

This file contains the linear order instance on the natural numbers.

See note [foundational algebra order theory].

## TODO

Move the `LinearOrder ℕ` instance here (https://github.com/leanprover-community/mathlib4/pull/13092).
-/

namespace Nat

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := zero_le

instance instNoMaxOrder : NoMaxOrder ℕ where
  exists_gt n := ⟨n + 1, n.lt_succ_self⟩

/-! ### Miscellaneous lemmas -/

@[simp high] protected lemma bot_eq_zero : ⊥ = 0 := rfl

/-- `Nat.find` is the minimum natural number satisfying a predicate `p`. -/
lemma isLeast_find {p : ℕ → Prop} [DecidablePred p] (hp : ∃ n, p n) :
    IsLeast {n | p n} (Nat.find hp) :=
  ⟨Nat.find_spec hp, fun _ ↦ Nat.find_min' hp⟩

end Nat

/-- `Nat.find` is the minimum element of a nonempty set of natural numbers. -/
lemma Set.Nonempty.isLeast_natFind {s : Set ℕ} [DecidablePred (· ∈ s)] (hs : s.Nonempty) :
    IsLeast s (Nat.find hs) :=
  Nat.isLeast_find hs

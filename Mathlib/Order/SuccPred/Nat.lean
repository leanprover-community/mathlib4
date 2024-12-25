/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import Mathlib.Order.SuccPred.LinearLocallyFinite
import Mathlib.Order.Interval.Finset.Nat

/-!
# The order-theoretic successor function on `Nat`
-/

namespace Nat

/-- The order-theoretic successor function on `Nat` is what it should be. -/
lemma orderSucc_eq_succ (n : ℕ) :
    Order.succ n = n + 1 := by
  apply le_antisymm
  · apply LinearLocallyFiniteOrder.succFn_le_of_lt
    exact lt_add_one n
  · rw [add_one_le_iff]
    exact lt_of_not_ge fun h ↦ not_isMax _ (LinearLocallyFiniteOrder.isMax_of_succFn_le _ h)

end Nat

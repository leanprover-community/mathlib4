/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import Mathlib.Algebra.Group.Nat
import Mathlib.Algebra.Order.Sub.Defs
import Mathlib.Data.Nat.Defs

/-!
# Ordered subtraction on the naturals

-/

assert_not_exists OrderedCommMonoid

namespace Nat

/-! ### Instance -/

instance instOrderedSub : OrderedSub ℕ := by
  refine ⟨fun m n k ↦ ?_⟩
  induction n generalizing k with
  | zero => simp
  | succ n ih => simp only [sub_succ, pred_le_iff, ih, succ_add, add_succ]

end Nat

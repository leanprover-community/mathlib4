/-
Copyright (c) 2025 Christoper Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/

import Mathlib.Order.Chain
import Mathlib.Order.Sublattice

/-!
# Nests
-/

variable (α : Type*)

namespace Nest

/-- A Nest is a Sublattice -/
def toSublattice [Lattice α] [OrderTop α] [OrderBot α] (s : Nest α) : Sublattice α where
  carrier := s.carrier
  supClosed' := by
    intro _ ha _ hb
    cases s.chain.total ha hb with
      | inl h => rw [sup_of_le_right h]; exact hb
      | inr h => rw [sup_of_le_left h]; exact ha
  infClosed' := by
    intro _ ha _ hb
    cases s.chain.total ha hb with
      | inl h => rw [inf_of_le_left h]; exact ha
      | inr h => rw [inf_of_le_right h]; exact hb

end Nest

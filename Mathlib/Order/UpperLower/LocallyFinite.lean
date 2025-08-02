/-
Copyright (c) 2023 Yaël Dillies, Sara Rousta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.UpperLower.Closure

/-!
# Upper and lower sets in a locally finite order

In this file we characterise the interaction of `UpperSet`/`LowerSet` and `LocallyFiniteOrder`.
-/


namespace Set

variable {α : Type*} [Preorder α] {s : Set α}

protected theorem Finite.upperClosure [LocallyFiniteOrderTop α] (hs : s.Finite) :
    (upperClosure s : Set α).Finite := by
  rw [coe_upperClosure]
  exact hs.biUnion fun _ _ => finite_Ici _

protected theorem Finite.lowerClosure [LocallyFiniteOrderBot α] (hs : s.Finite) :
    (lowerClosure s : Set α).Finite := by
  rw [coe_lowerClosure]
  exact hs.biUnion fun _ _ => finite_Iic _

end Set

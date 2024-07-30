/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Init.Algebra.Classes
import Mathlib.Data.Ordering.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.TypeStar
import Batteries.Classes.Order

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

# Orders

Defines classes for preorders, partial orders, and linear orders
and proves some basic lemmas about them.
-/

set_option linter.deprecated false

universe u
variable {α : Type u}

section Preorder

/-!
### Definition of `Preorder` and lemmas about types with a `Preorder`
-/

variable [Preorder α]

@[deprecated (since := "2024-07-30")]
theorem le_not_le_of_lt : ∀ {a b : α}, a < b → a ≤ b ∧ ¬b ≤ a
  | _a, _b, hab => lt_iff_le_not_le.mp hab

end Preorder

section LinearOrder

variable [LinearOrder α]

attribute [local instance] LinearOrder.decidableLE

@[deprecated (since := "2024-07-30")]
instance : IsTotalPreorder α (· ≤ ·) where
  trans := @le_trans _ _
  total := le_total

-- TODO(Leo): decide whether we should keep this instance or not
@[deprecated (since := "2024-07-30")]
instance isStrictWeakOrder_of_linearOrder : IsStrictWeakOrder α (· < ·) :=
  have : IsTotalPreorder α (· ≤ ·) := by infer_instance -- Porting note: added
  isStrictWeakOrder_of_isTotalPreorder lt_iff_not_ge

end LinearOrder

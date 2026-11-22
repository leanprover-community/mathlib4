/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Topology.Order.OrderClosed

/-!
# The equality order

Every type has a partial order in which two elements are comparable exactly when they are equal.
-/

@[expose] public section

namespace PartialOrder

/-- The partial order in which `a ≤ b` means `a = b`. -/
@[instance_reducible]
def eqOrder (α : Type*) : PartialOrder α where
  le := Eq
  le_refl := Eq.refl
  le_trans _ _ _ := Eq.trans
  le_antisymm _ _ h _ := h

namespace eqOrder

attribute [local instance] PartialOrder.eqOrder

variable (α : Type*)

/-- Addition preserves the equality order. -/
theorem isOrderedAddMonoid [AddCommMonoid α] :
    IsOrderedAddMonoid α :=
  { add_le_add_left _ _ h c := congrArg (· + c) h }

/-- Scalar multiplication preserves the equality order. -/
theorem posSMulMono (R : Type*) [Zero R] [Preorder R] [SMul R α] :
    PosSMulMono R α := by
  constructor
  intro a ha b1 b2 hb
  congr

/-- Principal upper sets are singletons in the equality order. -/
theorem Ici_eq_singleton (a : α) : Set.Ici a = {a} := by
  ext x
  rw [Set.mem_Ici, Set.mem_singleton_iff]
  exact eq_comm

/-- Principal upper sets are closed in the equality order on a T₁ space. -/
theorem closedIciTopology [TopologicalSpace α] [T1Space α] :
    ClosedIciTopology α := by
  constructor
  intro a
  rw [Ici_eq_singleton α a]
  exact isClosed_singleton

end eqOrder
end PartialOrder

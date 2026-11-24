/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Order.Defs.PartialOrders
public import Mathlib.Topology.Order.OrderClosed

/-!
# Properties of the discrete order

In the discrete order, monotonicity properties hold trivially.
-/

public section

namespace PartialOrder

namespace DiscreteOrder

variable {α : Type*} [PartialOrder α] [hd : PartialOrder.DiscreteOrder α]

/-- Addition preserves the discrete order. -/
instance [AddCommMonoid α] : IsOrderedAddMonoid α where
  add_le_add_left _ _ _ _ := by
    rw [le_iff_eq]
    congr
    rwa [← hd.le_iff_eq _ _]

/-- Scalar multiplication preserves the discrete order. -/
instance (R : Type*) [Zero R] [Preorder R] [SMul R α] : PosSMulMono R α := by
  constructor
  intro a ha b1 b2 hb
  rw [le_iff_eq]
  congr
  rwa [← hd.le_iff_eq _ _]

/-- Principal upper sets in the discrete order are singletons. -/
theorem Ici_eq_singleton (a : α) : Set.Ici a = {a} := by
  ext x
  rw [Set.mem_Ici, Set.mem_singleton_iff]
  rw [hd.le_iff_eq _ _]
  exact eq_comm

/-- Principal upper sets in the discrete order are singletons closed on a T₁ space. -/
instance [TopologicalSpace α] [T1Space α] : ClosedIciTopology α := by
  constructor
  intro a
  rw [Ici_eq_singleton a]
  exact isClosed_singleton

end DiscreteOrder
end PartialOrder

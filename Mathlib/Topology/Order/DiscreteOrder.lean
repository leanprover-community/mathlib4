/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Order.OrderOnOrders
public import Mathlib.Topology.Order.OrderClosed

/-!
# Closed intervals in the discrete order
-/

public section

namespace PartialOrder.DiscreteOrder

variable {α : Type*} [PartialOrder α] [hd : PartialOrder.DiscreteOrder α]

/-- Principal upper sets in the discrete order are singletons. -/
theorem Ici_eq_singleton (a : α) : Set.Ici a = {a} := by
  ext x
  rw [Set.mem_Ici, Set.mem_singleton_iff]
  rw [hd.eq_bot]
  exact eq_comm

/-- Principal upper sets in the discrete order are singletons closed on a T₁ space. -/
instance [TopologicalSpace α] [T1Space α] : ClosedIciTopology α := by
  constructor
  intro a
  rw [Ici_eq_singleton a]
  exact isClosed_singleton

end PartialOrder.DiscreteOrder

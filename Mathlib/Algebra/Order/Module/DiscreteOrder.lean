/-
Copyright (c) 2026 Pavel Zorin-Kranich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pavel Zorin-Kranich
-/
module

public import Mathlib.Algebra.Order.Module.Defs
public import Mathlib.Algebra.Order.Monoid.DiscreteOrder

/-!
# Discrete order on modules
-/

public section

namespace PartialOrder.DiscreteOrder

variable {α : Type*} [PartialOrder α] [hd : PartialOrder.DiscreteOrder α]

/-- Scalar multiplication preserves the discrete order. -/
instance posSMulMono (R : Type*) [Zero R] [Preorder R] [SMul R α] : PosSMulMono R α := by
  constructor
  intro a ha b1 b2 hb
  rw [hd.eq_bot] at hb ⊢
  congr

instance sMulPosMono (R : Type*) [Preorder R] [Monoid R] [AddMonoid α] [DistribMulAction R α] :
    SMulPosMono R α := by
  constructor
  intro b hb a1 a2 ha
  rw [hd.eq_bot] at hb ⊢
  rw [← hb, smul_zero, smul_zero]
  congr

instance isOrderedModule (R : Type*) [Zero R] [Preorder R] [Monoid R]
    [AddMonoid α] [DistribMulAction R α] : IsOrderedModule R α where
  toPosSMulMono := inferInstance
  toSMulPosMono := inferInstance

end PartialOrder.DiscreteOrder

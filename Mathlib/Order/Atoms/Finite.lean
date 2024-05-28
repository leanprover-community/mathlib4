/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Set.Finite
import Mathlib.Order.Atoms

#align_import order.atoms.finite from "leanprover-community/mathlib"@"d6fad0e5bf2d6f48da9175d25c3dc5706b3834ce"

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

This module contains some results on atoms and simple lattices in the finite context.

## Main results
  * `Finite.to_isAtomic`, `Finite.to_isCoatomic`: Finite partial orders with bottom resp. top
    are atomic resp. coatomic.

-/


variable {α β : Type*}

namespace IsSimpleOrder

section DecidableEq

/- It is important that `IsSimpleOrder` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply. -/
instance (priority := 200) {α} [DecidableEq α] [LE α] [BoundedOrder α] [IsSimpleOrder α] :
    Fintype α :=
  Fintype.ofEquiv Bool equivBool.symm

end DecidableEq

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

variable [PartialOrder α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} := by
  change Finset.map _ (Finset.univ : Finset Bool) = _
  rw [Fintype.univ_bool]
  simp only [Finset.map_insert, Function.Embedding.coeFn_mk, Finset.map_singleton]
  rfl
#align fintype.is_simple_order.univ Fintype.IsSimpleOrder.univ

theorem card : Fintype.card α = 2 :=
  (Fintype.ofEquiv_card _).trans Fintype.card_bool
#align fintype.is_simple_order.card Fintype.IsSimpleOrder.card

end IsSimpleOrder

end Fintype

namespace Bool

instance : IsSimpleOrder Bool :=
  ⟨fun a => by
    rw [← Finset.mem_singleton, Or.comm, ← Finset.mem_insert, top_eq_true, bot_eq_false, ←
      Fintype.univ_bool]
    apply Finset.mem_univ⟩

end Bool

section Fintype

open Finset

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_isCoatomic [PartialOrder α] [OrderTop α] [Finite α] :
    IsCoatomic α := by
  refine IsCoatomic.mk fun b => or_iff_not_imp_left.2 fun ht => ?_
  obtain ⟨c, hc, hmax⟩ :=
    Set.Finite.exists_maximal_wrt id { x : α | b ≤ x ∧ x ≠ ⊤ } (Set.toFinite _) ⟨b, le_rfl, ht⟩
  refine ⟨c, ⟨hc.2, fun y hcy => ?_⟩, hc.1⟩
  by_contra hyt
  obtain rfl : c = y := hmax y ⟨hc.1.trans hcy.le, hyt⟩ hcy.le
  exact (lt_self_iff_false _).mp hcy
#align finite.to_is_coatomic Finite.to_isCoatomic

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_isAtomic [PartialOrder α] [OrderBot α] [Finite α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp Finite.to_isCoatomic
#align finite.to_is_atomic Finite.to_isAtomic

end Fintype

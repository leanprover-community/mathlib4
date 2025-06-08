/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Atoms
import Mathlib.Order.Interval.Finset.Defs
import Mathlib.Order.Preorder.Finite

/-!
# Atoms, Coatoms, Simple Lattices, and Finiteness

This module contains some results on atoms and simple lattices in the finite context.

## Main results
* `Finite.to_isAtomic`, `Finite.to_isCoatomic`: Finite partial orders with bottom resp. top
  are atomic resp. coatomic.

-/


variable {α β : Type*}

namespace IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α]

section DecidableEq

/- It is important that `IsSimpleOrder` is the last type-class argument of this instance,
so that type-class inference fails quickly if it doesn't apply. -/
instance (priority := 200) [DecidableEq α] : Fintype α :=
  Fintype.ofEquiv Bool equivBool.symm

end DecidableEq

instance (priority := 200) : Finite α := by classical infer_instance

end IsSimpleOrder

namespace Fintype

namespace IsSimpleOrder

variable [LE α] [BoundedOrder α] [IsSimpleOrder α] [DecidableEq α]

theorem univ : (Finset.univ : Finset α) = {⊤, ⊥} := by
  change Finset.map _ (Finset.univ : Finset Bool) = _
  rw [Fintype.univ_bool]
  simp only [Finset.map_insert, Function.Embedding.coeFn_mk, Finset.map_singleton]
  rfl

theorem card : Fintype.card α = 2 :=
  (Fintype.ofEquiv_card _).trans Fintype.card_bool

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
    Set.Finite.exists_maximalFor id { x : α | b ≤ x ∧ x ≠ ⊤ } (Set.toFinite _) ⟨b, le_rfl, ht⟩
  refine ⟨c, ⟨hc.2, fun y hcy => ?_⟩, hc.1⟩
  by_contra hyt
  exact not_lt_iff_le_imp_ge.2 (hmax ⟨hc.1.trans hcy.le, hyt⟩) hcy

-- see Note [lower instance priority]
instance (priority := 100) Finite.to_isAtomic [PartialOrder α] [OrderBot α] [Finite α] :
    IsAtomic α :=
  isCoatomic_dual_iff_isAtomic.mp Finite.to_isCoatomic

end Fintype

section LocallyFinite

variable [Preorder α] [LocallyFiniteOrder α]

instance : IsStronglyAtomic α where
  exists_covBy_le_of_lt a b hab := by
    obtain ⟨x, hx, hxmin⟩ := (LocallyFiniteOrder.finsetIoc a b).exists_minimal
      ⟨b, by simpa [LocallyFiniteOrder.finset_mem_Ioc]⟩
    simp only [LocallyFiniteOrder.finset_mem_Ioc] at hx hxmin
    exact ⟨x, ⟨hx.1, fun c hac hcx ↦ hcx.not_ge <| hxmin ⟨hac, hcx.le.trans hx.2⟩ hcx.le⟩, hx.2⟩

instance : IsStronglyCoatomic α := by
  rw [← isStronglyAtomic_dual_iff_is_stronglyCoatomic]; infer_instance

end LocallyFinite

section IsStronglyAtomic

variable [PartialOrder α] {a : α}

theorem exists_covby_infinite_Ici_of_infinite_Ici [IsStronglyAtomic α]
    (ha : (Set.Ici a).Infinite) (hfin : {x | a ⋖ x}.Finite) :
    ∃ b, a ⋖ b ∧ (Set.Ici b).Infinite := by
  by_contra! h
  refine ((hfin.biUnion (t := Set.Ici) (by simpa using h)).subset (fun b hb ↦ ?_)).not_infinite
    (ha.diff (Set.finite_singleton a))
  obtain ⟨x, hax, hxb⟩ := ((show a ≤ b from hb.1).lt_of_ne (Ne.symm hb.2)).exists_covby_le
  exact Set.mem_biUnion hax hxb

theorem exists_covby_infinite_Iic_of_infinite_Iic [IsStronglyCoatomic α]
    (ha : (Set.Iic a).Infinite) (hfin : {x | x ⋖ a}.Finite) :
    ∃ b, b ⋖ a ∧ (Set.Iic b).Infinite := by
  simp_rw [← toDual_covBy_toDual_iff (α := α)] at hfin ⊢
  exact exists_covby_infinite_Ici_of_infinite_Ici (α := αᵒᵈ) ha hfin

end IsStronglyAtomic

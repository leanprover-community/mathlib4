/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Order.CompleteLatticeIntervals

#align_import algebra.order.nonneg.ring from "leanprover-community/mathlib"@"422e70f7ce183d2900c586a8cda8381e788a0c62"

/-!
# Order instances on nonnegative elements.

-/

open Set

variable {α : Type*}

namespace Nonneg

/-- This instance uses data fields from `Subtype.partialOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a ≤ x } :=
  { Set.Ici.orderBot with }
#align nonneg.order_bot Nonneg.orderBot

theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl
#align nonneg.bot_eq Nonneg.bot_eq

instance noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a ≤ x } :=
  show NoMaxOrder (Ici a) by infer_instance
#align nonneg.no_max_order Nonneg.noMaxOrder

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a ≤ x } :=
  Set.Ici.semilatticeSup
#align nonneg.semilattice_sup Nonneg.semilatticeSup

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  Set.Ici.semilatticeInf
#align nonneg.semilattice_inf Nonneg.semilatticeInf

instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a ≤ x } :=
  Set.Ici.distribLattice
#align nonneg.distrib_lattice Nonneg.distribLattice

instance instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a ≤ x } :=
  show DenselyOrdered (Ici a) from Set.instDenselyOrdered
#align nonneg.densely_ordered Nonneg.instDenselyOrdered

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`. -/
protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  { @ordConnectedSubsetConditionallyCompleteLinearOrder α (Set.Ici a) _ ⟨⟨a, le_rfl⟩⟩ _ with }
#align nonneg.conditionally_complete_linear_order Nonneg.conditionallyCompleteLinearOrder

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrderBot`.

This instance uses data fields from `Subtype.linearOrder` to help type-class inference.
The `Set.Ici` data fields are definitionally equal, but that requires unfolding semireducible
definitions, so type-class inference won't see this. -/
protected noncomputable abbrev conditionallyCompleteLinearOrderBot
    [ConditionallyCompleteLinearOrder α] (a : α) :
    ConditionallyCompleteLinearOrderBot { x : α // a ≤ x } :=
  { Nonneg.orderBot, Nonneg.conditionallyCompleteLinearOrder with
    csSup_empty := by
      rw [@subset_sSup_def α (Set.Ici a) _ _ ⟨⟨a, le_rfl⟩⟩]; simp [bot_eq] }
#align nonneg.conditionally_complete_linear_order_bot Nonneg.conditionallyCompleteLinearOrderBot

/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Order.CompleteLatticeIntervals
public import Mathlib.Order.LatticeIntervals

/-!
# Lattice structures on the type of nonnegative elements

-/

@[expose] public section
assert_not_exists Ring
assert_not_exists IsOrderedMonoid

open Set

variable {α : Type*}

namespace Nonneg

instance orderBot [Preorder α] {a : α} : OrderBot { x : α // a ≤ x } :=
  inferInstanceAs <| OrderBot (Ici a)

theorem bot_eq [Preorder α] {a : α} : (⊥ : { x : α // a ≤ x }) = ⟨a, le_rfl⟩ :=
  rfl

instance noMaxOrder [PartialOrder α] [NoMaxOrder α] {a : α} : NoMaxOrder { x : α // a ≤ x } :=
  inferInstanceAs <| NoMaxOrder (Ici a)

instance semilatticeSup [SemilatticeSup α] {a : α} : SemilatticeSup { x : α // a ≤ x } :=
  inferInstanceAs <| SemilatticeSup (Ici a)

instance semilatticeInf [SemilatticeInf α] {a : α} : SemilatticeInf { x : α // a ≤ x } :=
  inferInstanceAs <| SemilatticeInf (Ici a)

instance distribLattice [DistribLattice α] {a : α} : DistribLattice { x : α // a ≤ x } :=
  inferInstanceAs <| DistribLattice (Ici a)

instance instDenselyOrdered [Preorder α] [DenselyOrdered α] {a : α} :
    DenselyOrdered { x : α // a ≤ x } :=
  inferInstanceAs <| DenselyOrdered (Ici a)

/-- If `sSup ∅ ≤ a` then `{x : α // a ≤ x}` is a `ConditionallyCompleteLinearOrder`. -/
protected noncomputable abbrev conditionallyCompleteLinearOrder [ConditionallyCompleteLinearOrder α]
    {a : α} : ConditionallyCompleteLinearOrder { x : α // a ≤ x } :=
  -- TODO: missing `Inhabited (Ici a)` instance
  haveI : Inhabited (Ici a) := ⟨a, le_rfl⟩
  inferInstanceAs <| ConditionallyCompleteLinearOrder (Ici a)


set_option backward.isDefEq.respectTransparency false in
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

end Nonneg

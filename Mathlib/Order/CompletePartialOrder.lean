/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.BoundedOrder.Basic
public import Mathlib.Order.OmegaCompletePartialOrder
public import Mathlib.Order.ConditionallyCompletePartialOrder.Defs

/-!
# Complete Partial Orders

This file considers complete partial orders (sometimes called directedly complete partial orders).
These are partial orders for which every directed set has a least upper bound.

## Main declarations

- `CompletePartialOrder`: Typeclass for (directly) complete partial orders.

## Main statements

- `CompletePartialOrder.toOmegaCompletePartialOrder`: A complete partial order is an ω-complete
  partial order.
- `CompleteLattice.toCompletePartialOrder`: A complete lattice is a complete partial order.

## References

- [B. A. Davey and H. A. Priestley, Introduction to lattices and order][davey_priestley]

## Tags

complete partial order, directedly complete partial order
-/

@[expose] public section

variable {ι : Sort*} {α β : Type*}

section CompletePartialOrder

/--
Complete partial orders are partial orders where every directed set has a least upper bound.
-/
class CompletePartialOrder (α : Type*) extends PartialOrder α, SupSet α, OrderBot α where
  /-- For each directed set `d`, `sSup d` is the least upper bound of `d`. -/
  lubOfPredirected : ∀ d, PredirectedOn (· ≤ ·) d → IsLUB d (sSup d)

/-- Create a `CompletePartialOrder` from a `PartialOrder` and `SupSet`
such that for every directed set `d`, `sSup d` is the least upper bound of `d`.

The bottom element is defined as `sSup ∅`.
-/
@[reducible]
def CompletePartialOrder.ofLubOfPredirected (α : Type*) [H1 : PartialOrder α] [H2 : SupSet α]
    (lub_of_predirected : ∀ d : Set α, PredirectedOn (· ≤ ·) d → IsLUB d (sSup d)) :
    CompletePartialOrder α where
  __ := H1; __ := H2
  bot := sSup ∅
  bot_le := isLUB_empty_iff.mp <| lub_of_predirected ∅ IsChain.empty.predirectedOn
  lubOfPredirected := lub_of_predirected

variable [CompletePartialOrder α] [Preorder β] {f : ι → α} {d : Set α} {a : α}

protected lemma PredirectedOn.isLUB_sSup : PredirectedOn (· ≤ ·) d → IsLUB d (sSup d) :=
CompletePartialOrder.lubOfPredirected _

protected lemma PredirectedOn.le_sSup (hd : PredirectedOn (· ≤ ·) d) (ha : a ∈ d) : a ≤ sSup d :=
hd.isLUB_sSup.1 ha

protected lemma PredirectedOn.sSup_le (hd : PredirectedOn (· ≤ ·) d) (ha : ∀ b ∈ d, b ≤ a) :
    sSup d ≤ a :=
hd.isLUB_sSup.2 ha

protected lemma Predirected.le_iSup (hf : Predirected (· ≤ ·) f) (i : ι) : f i ≤ ⨆ j, f j :=
hf.predirectedOn_range.le_sSup <| Set.mem_range_self _

protected lemma Predirected.iSup_le (hf : Predirected (· ≤ ·) f) (ha : ∀ i, f i ≤ a) :
    ⨆ i, f i ≤ a :=
hf.predirectedOn_range.sSup_le <| Set.forall_mem_range.2 ha

--TODO: We could mimic more `sSup`/`iSup` lemmas

/-- Scott-continuity takes on a simpler form in complete partial orders. -/
lemma CompletePartialOrder.scottContinuous {f : α → β} :
    ScottContinuous f ↔
    ∀ ⦃d : Set α⦄, d.Nonempty → PredirectedOn (· ≤ ·) d → IsLUB (f '' d) (f (sSup d)) := by
  refine ⟨fun h d hd₁ hd₂ ↦ h hd₁ hd₂ hd₂.isLUB_sSup, fun h d hne hd a hda ↦ ?_⟩
  rw [hda.unique hd.isLUB_sSup]
  exact h hne hd

open OmegaCompletePartialOrder

/-- A complete partial order is an ω-complete partial order. -/
instance (priority := 100) CompletePartialOrder.toOmegaCompletePartialOrder :
    OmegaCompletePartialOrder α where
  ωSup c := ⨆ n, c n
  le_ωSup c := c.predirected.le_iSup
  ωSup_le c _ := c.predirected.iSup_le

/-- A complete partial order is an conditionally complete partial order. -/
instance (priority := 100) : ConditionallyCompletePartialOrderSup α where
  isLUB_csSup_of_predirected _ h_dir _ _ := h_dir.isLUB_sSup

end CompletePartialOrder

/-- A complete lattice is a complete partial order. -/
instance (priority := 100) CompleteLattice.toCompletePartialOrder [CompleteLattice α] :
    CompletePartialOrder α where
  sSup := sSup
  lubOfPredirected _ _ := isLUB_sSup _

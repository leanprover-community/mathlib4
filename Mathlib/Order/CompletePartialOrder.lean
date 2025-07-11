/-
Copyright (c) 2023 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Order.OmegaCompletePartialOrder

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

variable {ι : Sort*} {α β : Type*}

section CompletePartialOrder

/--
Complete partial orders are partial orders where every directed set has a least upper bound.
-/
class CompletePartialOrder (α : Type*) extends PartialOrder α, SupSet α where
  /-- For each directed set `d`, `sSup d` is the least upper bound of `d`. -/
  lubOfDirected : ∀ d, DirectedOn (· ≤ ·) d → IsLUB d (sSup d)

variable [CompletePartialOrder α] [Preorder β] {f : ι → α} {d : Set α} {a : α}

protected lemma DirectedOn.isLUB_sSup : DirectedOn (· ≤ ·) d → IsLUB d (sSup d) :=
CompletePartialOrder.lubOfDirected _

protected lemma DirectedOn.le_sSup (hd : DirectedOn (· ≤ ·) d) (ha : a ∈ d) : a ≤ sSup d :=
hd.isLUB_sSup.1 ha

protected lemma DirectedOn.sSup_le (hd : DirectedOn (· ≤ ·) d) (ha : ∀ b ∈ d, b ≤ a) : sSup d ≤ a :=
hd.isLUB_sSup.2 ha

protected lemma Directed.le_iSup (hf : Directed (· ≤ ·) f) (i : ι) : f i ≤ ⨆ j, f j :=
hf.directedOn_range.le_sSup <| Set.mem_range_self _

protected lemma Directed.iSup_le (hf : Directed (· ≤ ·) f) (ha : ∀ i, f i ≤ a) : ⨆ i, f i ≤ a :=
hf.directedOn_range.sSup_le <| Set.forall_mem_range.2 ha

--TODO: We could mimic more `sSup`/`iSup` lemmas

/-- Scott-continuity takes on a simpler form in complete partial orders. -/
lemma CompletePartialOrder.scottContinuous {f : α → β} :
    ScottContinuous f ↔
    ∀ ⦃d : Set α⦄, d.Nonempty → DirectedOn (· ≤ ·) d → IsLUB (f '' d) (f (sSup d)) := by
  refine ⟨fun h d hd₁ hd₂ ↦ h hd₁ hd₂ hd₂.isLUB_sSup, fun h d hne hd a hda ↦ ?_⟩
  rw [hda.unique hd.isLUB_sSup]
  exact h hne hd

open OmegaCompletePartialOrder

/-- A complete partial order is an ω-complete partial order. -/
instance CompletePartialOrder.toOmegaCompletePartialOrder : OmegaCompletePartialOrder α where
  ωSup c := ⨆ n, c n
  le_ωSup c := c.directed.le_iSup
  ωSup_le c _ := c.directed.iSup_le

end CompletePartialOrder

/-- A complete lattice is a complete partial order. -/
instance CompleteLattice.toCompletePartialOrder [CompleteLattice α] : CompletePartialOrder α where
  sSup := sSup
  lubOfDirected _ _ := isLUB_sSup _

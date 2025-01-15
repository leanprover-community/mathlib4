/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Aaron Anderson
-/
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.Antichain
import Mathlib.Order.OrderIsoNat

variable {α : Type*}

/-- A well quasi-order or WQO is a relation such that any infinite sequence contains an infinite
monotonic subsequence, or equivalently, two elements `f m` and `f n` with `m < n` and
`r (f m) (f n)`.

For a preorder, this is equivalent to having a well-founded order with no infinite antichains.

Despite the nomenclature, we don't require the relation to be preordered. Moreover, a well
quasi-order will not in general be a well-order. -/
def WellQuasiOrdered (r : α → α → Prop) : Prop :=
  ∀ f : ℕ → α, ∃ m n : ℕ, m < n ∧ r (f m) (f n)

theorem Finite.wellQuasiOrdered (r : α → α → Prop) [Finite α] [IsRefl α r] :
    WellQuasiOrdered r := by
  intro f
  obtain ⟨a, b, h, h'⟩ := Set.finite_univ.exists_lt_map_eq_of_forall_mem (f := f)
    fun _ ↦ Set.mem_univ _
  exact ⟨a, b, h, h' ▸ refl _⟩

/-- A typeclass for an ordered with a well quasi-ordered `≤` relation. -/
class WellQuasiOrderedLE (α : Type*) [LE α] where
  wqo : @WellQuasiOrdered α (· ≤ ·)

section Preorder
variable [Preorder α]

instance (priority := 100) Finite.to_wellQuasiOrderedLE [Finite α] : WellQuasiOrderedLE α where
  wqo := Finite.wellQuasiOrdered _

instance (priority := 100) WellQuasiOrderedLE.to_wellFoundedLT [WellQuasiOrderedLE α] :
    WellFoundedLT α := by
  rw [WellFoundedLT, isWellFounded_iff, wellFounded_iff_no_descending_seq]

  sorry

#exit

/-- A preorder is well quasi-ordered iff it's well-founded and has no infinite antichains. -/
theorem wellQuasiOrderedLE_iff :
    WellQuasiOrderedLE α ↔ WellFoundedLT α ∧ ∀ s : Set α, s.Finite → IsAntichain (· ≤ ·) s := by
  sorry

end Preorder

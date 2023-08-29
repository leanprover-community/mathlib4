/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import Mathlib.Data.Set.Lattice

#align_import data.set.accumulate from "leanprover-community/mathlib"@"207cfac9fcd06138865b5d04f7091e46d9320432"

/-!
# Accumulate

The function `Accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/


variable {α β γ : Type*} {s : α → Set β} {t : α → Set γ}

namespace Set

/-- `Accumulate s` is the union of `s y` for `y ≤ x`. -/
def Accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y
#align set.accumulate Set.Accumulate

theorem accumulate_def [LE α] {x : α} : Accumulate s x = ⋃ y ≤ x, s y :=
  rfl
#align set.accumulate_def Set.accumulate_def

@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ Accumulate s x ↔ ∃ y ≤ x, z ∈ s y := by
  simp_rw [accumulate_def, mem_iUnion₂, exists_prop]
  -- 🎉 no goals
#align set.mem_accumulate Set.mem_accumulate

theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ Accumulate s x := fun _ => mem_biUnion le_rfl
#align set.subset_accumulate Set.subset_accumulate

theorem monotone_accumulate [Preorder α] : Monotone (Accumulate s) := fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy
#align set.monotone_accumulate Set.monotone_accumulate

theorem biUnion_accumulate [Preorder α] (x : α) : ⋃ y ≤ x, Accumulate s y = ⋃ y ≤ x, s y := by
  apply Subset.antisymm
  -- ⊢ ⋃ (y : α) (_ : y ≤ x), Accumulate s y ⊆ ⋃ (y : α) (_ : y ≤ x), s y
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
    -- 🎉 no goals
  · exact iUnion₂_mono fun y _ => subset_accumulate
    -- 🎉 no goals
#align set.bUnion_accumulate Set.biUnion_accumulate

theorem iUnion_accumulate [Preorder α] : ⋃ x, Accumulate s x = ⋃ x, s x := by
  apply Subset.antisymm
  -- ⊢ ⋃ (x : α), Accumulate s x ⊆ ⋃ (x : α), s x
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    -- ⊢ ∀ (x : β) (x_1 x_2 : α), x_2 ≤ x_1 ∧ x ∈ s x_2 → ∃ i, x ∈ s i
    intro z x x' ⟨_, hz⟩
    -- ⊢ ∃ i, z ∈ s i
    exact ⟨x', hz⟩
    -- 🎉 no goals
  · exact iUnion_mono fun i => subset_accumulate
    -- 🎉 no goals
#align set.Union_accumulate Set.iUnion_accumulate

end Set

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
#align set.mem_accumulate Set.mem_accumulate

theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ Accumulate s x := fun _ => mem_biUnion le_rfl
#align set.subset_accumulate Set.subset_accumulate

theorem accumulate_subset_iUnion [Preorder α] (x : α) : Accumulate s x ⊆ ⋃ i, s i :=
  (biUnion_subset_biUnion_left (subset_univ _)).trans_eq (biUnion_univ _)

theorem monotone_accumulate [Preorder α] : Monotone (Accumulate s) := fun _ _ hxy =>
  biUnion_subset_biUnion_left fun _ hz => le_trans hz hxy
#align set.monotone_accumulate Set.monotone_accumulate

@[gcongr]
theorem accumulate_subset_accumulate [Preorder α] {x y} (h : x ≤ y) :
    Accumulate s x ⊆ Accumulate s y :=
  monotone_accumulate h

theorem biUnion_accumulate [Preorder α] (x : α) : ⋃ y ≤ x, Accumulate s y = ⋃ y ≤ x, s y := by
  apply Subset.antisymm
  · exact iUnion₂_subset fun y hy => monotone_accumulate hy
  · exact iUnion₂_mono fun y _ => subset_accumulate
#align set.bUnion_accumulate Set.biUnion_accumulate

theorem iUnion_accumulate [Preorder α] : ⋃ x, Accumulate s x = ⋃ x, s x := by
  apply Subset.antisymm
  · simp only [subset_def, mem_iUnion, exists_imp, mem_accumulate]
    intro z x x' ⟨_, hz⟩
    exact ⟨x', hz⟩
  · exact iUnion_mono fun i => subset_accumulate
#align set.Union_accumulate Set.iUnion_accumulate

end Set

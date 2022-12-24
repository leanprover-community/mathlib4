/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
Ported by: Anatole Dedecker

! This file was ported from Lean 3 source module data.set.accumulate
! leanprover-community/mathlib commit 207cfac9fcd06138865b5d04f7091e46d9320432
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.Set.Lattice

/-!
# Accumulate

The function `accumulate` takes a set `s` and returns `⋃ y ≤ x, s y`.
-/


variable {α β γ : Type _} {s : α → Set β} {t : α → Set γ}

namespace Set

/-- `accumulate s` is the union of `s y` for `y ≤ x`. -/
def accumulate [LE α] (s : α → Set β) (x : α) : Set β :=
  ⋃ y ≤ x, s y
#align set.accumulate Set.accumulate

variable {s}

theorem accumulate_def [LE α] {x : α} : accumulate s x = ⋃ y ≤ x, s y :=
  rfl
#align set.accumulate_def Set.accumulate_def

@[simp]
theorem mem_accumulate [LE α] {x : α} {z : β} : z ∈ accumulate s x ↔ ∃ y ≤ x, z ∈ s y :=
  mem_Union₂
#align set.mem_accumulate Set.mem_accumulate

theorem subset_accumulate [Preorder α] {x : α} : s x ⊆ accumulate s x := fun z => mem_bUnion le_rfl
#align set.subset_accumulate Set.subset_accumulate

theorem monotone_accumulate [Preorder α] : Monotone (accumulate s) := fun x y hxy =>
  bUnion_subset_bUnion_left fun z hz => le_trans hz hxy
#align set.monotone_accumulate Set.monotone_accumulate

theorem bUnion_accumulate [Preorder α] (x : α) : (⋃ y ≤ x, accumulate s y) = ⋃ y ≤ x, s y := by
  apply subset.antisymm
  · exact Union₂_subset fun y hy => monotone_accumulate hy
  · exact Union₂_mono fun y hy => subset_accumulate
#align set.bUnion_accumulate Set.bUnion_accumulate

theorem Union_accumulate [Preorder α] : (⋃ x, accumulate s x) = ⋃ x, s x := by
  apply subset.antisymm
  · simp only [subset_def, mem_Union, exists_imp, mem_accumulate]
    intro z x x' hx'x hz
    exact ⟨x', hz⟩
  · exact Union_mono fun i => subset_accumulate
#align set.Union_accumulate Set.Union_accumulate

end Set

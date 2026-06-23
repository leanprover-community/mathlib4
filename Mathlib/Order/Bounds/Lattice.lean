/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Set.Lattice.Image

/-!
# Unions and intersections of bounds

Some results about upper and lower bounds over collections of sets.

## Implementation notes

In a separate file as we need to import `Mathlib/Data/Set/Lattice.lean`.

-/

public section

variable {α : Type*} [Preorder α] {ι : Sort*} {s : ι → Set α}

open Set

@[to_dual]
theorem gc_upperBounds_lowerBounds : GaloisConnection
    (OrderDual.toDual ∘ upperBounds : Set α → (Set α)ᵒᵈ)
    (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ → Set α) := by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T ↦ forall₂_comm

@[to_dual (attr := simp)]
theorem upperBounds_iUnion :
    upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i) :=
  gc_upperBounds_lowerBounds.l_iSup

@[to_dual]
theorem isLUB_iUnion_iff_of_isLUB {u : ι → α} (hs : ∀ i, IsLUB (s i) (u i)) (c : α) :
    IsLUB (Set.range u) c ↔ IsLUB (⋃ i, s i) c := by
  refine isLUB_congr ?_
  simp_rw [range_eq_iUnion, upperBounds_iUnion, upperBounds_singleton, (hs _).upperBounds_eq]

@[deprecated isGLB_iUnion_iff_of_isGLB (since := "2026-06-04")]
theorem isGLB_iUnion_iff_of_isLUB {u : ι → α} (hs : ∀ i, IsGLB (s i) (u i)) (c : α) :
    IsGLB (Set.range u) c ↔ IsGLB (⋃ i, s i) c := by
  refine isGLB_congr ?_
  simp_rw [range_eq_iUnion, lowerBounds_iUnion, lowerBounds_singleton, (hs _).lowerBounds_eq]

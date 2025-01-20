/-
Copyright (c) 2024 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
import Mathlib.Data.Set.Lattice

/-!
# Unions and intersections of bounds

Some results about upper and lower bounds over collections of sets.

## Implementation notes

In a separate file as we need to import `Mathlib.Data.Set.Lattice`.

-/

variable {α : Type*} [Preorder α]

open Set

theorem gc_upperBounds_lowerBounds : GaloisConnection
    (OrderDual.toDual ∘ upperBounds : Set α → (Set α)ᵒᵈ)
    (lowerBounds ∘ OrderDual.ofDual : (Set α)ᵒᵈ → Set α) := by
  simpa [GaloisConnection, subset_def, mem_upperBounds, mem_lowerBounds]
    using fun S T ↦ forall₂_swap

theorem upperBounds_iUnion {ι : Sort*} {s : ι → Set α} :
    upperBounds (⋃ i, s i) = ⋂ i, upperBounds (s i) :=
  upperBounds_lowerBounds_gc.l_iSup

theorem lowerBounds_iUnion {ι : Sort*} {s : ι → Set α} :
    lowerBounds (⋃ i, s i) = ⋂ i, lowerBounds (s i) :=
  upperBounds_lowerBounds_gc.u_iInf

theorem isLUB_iUnion_iff_of_isLUB {ι : Sort*} {u : ι → α} {s : ι → Set α}
    (hs : ∀ i, IsLUB (s i) (u i)) (c : α) :
    IsLUB (Set.range u) c ↔ IsLUB (⋃ i, s i) c := by
  refine isLUB_congr ?_
  simp_rw [range_eq_iUnion, upperBounds_iUnion, upperBounds_singleton, (hs _).upperBounds_eq]

theorem isGLB_iUnion_iff_of_isLUB {ι : Sort*} {u : ι → α} {s : ι → Set α}
    (hs : ∀ (i : ι), IsGLB (s i) (u i)) (c : α) :
    IsGLB (Set.range u) c ↔ IsGLB (⋃ i, s i) c := by
  refine isGLB_congr ?_
  simp_rw [range_eq_iUnion, lowerBounds_iUnion, lowerBounds_singleton, IsGLB.lowerBounds_eq (hs _)]

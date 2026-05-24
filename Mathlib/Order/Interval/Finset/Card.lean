/-
Copyright (c) 2026 Snir Broshi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Snir Broshi
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Defs

/-!
# Cardinalities of intervals

Cardinalities of intervals can be computed using finsets in locally finite orders.
-/

public section

open Finset

variable {α : Type*}

section Preorder

variable [Preorder α]

section LocallyFiniteOrder

variable [LocallyFiniteOrder α]

@[to_dual self]
theorem Set.cardinalMk_Icc (a b : α) : Cardinal.mk (Set.Icc a b) = #(Finset.Icc a b) := by
  simp

@[to_dual self]
theorem Set.encard_Icc (a b : α) : (Set.Icc a b).encard = #(Finset.Icc a b) := by
  simp [← Finset.coe_Icc]

@[to_dual self]
theorem Set.ncard_Icc (a b : α) : (Set.Icc a b).ncard = #(Finset.Icc a b) := by
  simp [← Finset.coe_Icc]

@[to_dual (reorder := a b)]
theorem Set.cardinalMk_Ico (a b : α) : Cardinal.mk (Set.Ico a b) = #(Finset.Ico a b) := by
  simp

@[to_dual (reorder := a b)]
theorem Set.encard_Ico (a b : α) : (Set.Ico a b).encard = #(Finset.Ico a b) := by
  simp [← Finset.coe_Ico]

@[to_dual (reorder := a b)]
theorem Set.ncard_Ico (a b : α) : (Set.Ico a b).ncard = #(Finset.Ico a b) := by
  simp [← Finset.coe_Ico]

@[to_dual self]
theorem Set.cardinalMk_Ioo (a b : α) : Cardinal.mk (Set.Ioo a b) = #(Finset.Ioo a b) := by
  simp

@[to_dual self]
theorem Set.encard_Ioo (a b : α) : (Set.Ioo a b).encard = #(Finset.Ioo a b) := by
  simp [← Finset.coe_Ioo]

@[to_dual self]
theorem Set.ncard_Ioo (a b : α) : (Set.Ioo a b).ncard = #(Finset.Ioo a b) := by
  simp [← Finset.coe_Ioo]

end LocallyFiniteOrder

section LocallyFiniteOrderTop

variable [LocallyFiniteOrderTop α]

@[to_dual]
theorem Set.cardinalMk_Ici (a : α) : Cardinal.mk (Set.Ici a) = #(Finset.Ici a) := by
  simp

@[to_dual]
theorem Set.encard_Ici (a : α) : (Set.Ici a).encard = #(Finset.Ici a) := by
  simp [← Finset.coe_Ici]

@[to_dual]
theorem Set.ncard_Ici (a : α) : (Set.Ici a).ncard = #(Finset.Ici a) := by
  simp [← Finset.coe_Ici]

@[to_dual]
theorem Set.cardinalMk_Ioi (a : α) : Cardinal.mk (Set.Ioi a) = #(Finset.Ioi a) := by
  simp

@[to_dual]
theorem Set.encard_Ioi (a : α) : (Set.Ioi a).encard = #(Finset.Ioi a) := by
  simp [← Finset.coe_Ioi]

@[to_dual]
theorem Set.ncard_Ioi (a : α) : (Set.Ioi a).ncard = #(Finset.Ioi a) := by
  simp [← Finset.coe_Ioi]

end LocallyFiniteOrderTop

end Preorder

section Lattice

variable [Lattice α] [LocallyFiniteOrder α]

theorem Set.cardinalMk_uIcc (a b : α) : Cardinal.mk (Set.uIcc a b) = #(Finset.uIcc a b) := by
  simp

theorem Set.encard_uIcc (a b : α) : (Set.uIcc a b).encard = #(Finset.uIcc a b) := by
  simp [← Finset.coe_uIcc]

theorem Set.ncard_uIcc (a b : α) : (Set.uIcc a b).ncard = #(Finset.uIcc a b) := by
  simp [← Finset.coe_uIcc]

end Lattice

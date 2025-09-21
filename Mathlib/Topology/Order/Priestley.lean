/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Connected.TotallyDisconnected

/-!
# Priestley spaces

This file defines Priestley spaces. A Priestley space is an ordered compact topological space such
that any two distinct points can be separated by a clopen upper set.

## Main declarations

* `PriestleySpace`: Prop-valued mixin stating the Priestley separation axiom: Any two distinct
  points can be separated by a clopen upper set.

## Implementation notes

We do not include compactness in the definition, so a Priestley space is to be declared as follows:
`[Preorder α] [TopologicalSpace α] [CompactSpace α] [PriestleySpace α]`

## References

* [Wikipedia, *Priestley space*](https://en.wikipedia.org/wiki/Priestley_space)
* [Davey, Priestley *Introduction to Lattices and Order*][davey_priestley]
-/


open Set

variable {α : Type*}

/-- A Priestley space is an ordered topological space such that any two distinct points can be
separated by a clopen upper set. Compactness is often assumed, but we do not include it here. -/
class PriestleySpace (α : Type*) [Preorder α] [TopologicalSpace α] : Prop where
  priestley {x y : α} : ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U

variable [TopologicalSpace α]

section Preorder

variable [Preorder α] [PriestleySpace α] {x y : α}

theorem exists_isClopen_upper_of_not_le :
    ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U :=
  PriestleySpace.priestley

theorem exists_isClopen_lower_of_not_le (h : ¬x ≤ y) :
    ∃ U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y ∈ U :=
  let ⟨U, hU, hU', hx, hy⟩ := exists_isClopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩

end Preorder

section PartialOrder

variable [PartialOrder α] [PriestleySpace α] {x y : α}

theorem exists_isClopen_upper_or_lower_of_ne (h : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ y ∉ U := by
  obtain h | h := h.not_le_or_not_ge
  · exact (exists_isClopen_upper_of_not_le h).imp fun _ ↦ And.imp_right <| And.imp_left Or.inl
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_isClopen_lower_of_not_le h
    exact ⟨U, hU, Or.inr hU', hx, hy⟩

-- See note [lower instance priority]
instance (priority := 100) PriestleySpace.toTotallySeparatedSpace : TotallySeparatedSpace α where
  isTotallySeparated_univ _ _ _ _ h :=
    (exists_isClopen_upper_or_lower_of_ne h).elim fun U ⟨hU, _, hx, hy⟩ =>
      ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, hy,
        union_compl_self U ▸ subset_rfl, disjoint_compl_right⟩

end PartialOrder

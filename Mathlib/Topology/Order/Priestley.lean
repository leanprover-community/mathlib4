/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Separation

#align_import topology.order.priestley from "leanprover-community/mathlib"@"4c19a16e4b705bf135cf9a80ac18fcc99c438514"

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
#align priestley_space PriestleySpace

variable [TopologicalSpace α]

section Preorder

variable [Preorder α] [PriestleySpace α] {x y : α}

theorem exists_clopen_upper_of_not_le :
    ¬x ≤ y → ∃ U : Set α, IsClopen U ∧ IsUpperSet U ∧ x ∈ U ∧ y ∉ U :=
  PriestleySpace.priestley
#align exists_clopen_upper_of_not_le exists_clopen_upper_of_not_le

theorem exists_clopen_lower_of_not_le (h : ¬x ≤ y) :
    ∃ U : Set α, IsClopen U ∧ IsLowerSet U ∧ x ∉ U ∧ y ∈ U :=
  let ⟨U, hU, hU', hx, hy⟩ := exists_clopen_upper_of_not_le h
  ⟨Uᶜ, hU.compl, hU'.compl, Classical.not_not.2 hx, hy⟩
#align exists_clopen_lower_of_not_le exists_clopen_lower_of_not_le

end Preorder

section PartialOrder

variable [PartialOrder α] [PriestleySpace α] {x y : α}

theorem exists_clopen_upper_or_lower_of_ne (h : x ≠ y) :
    ∃ U : Set α, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ y ∉ U := by
  obtain h | h := h.not_le_or_not_le
  -- ⊢ ∃ U, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ ¬y ∈ U
  · exact (exists_clopen_upper_of_not_le h).imp fun _ ↦ And.imp_right <| And.imp_left Or.inl
    -- 🎉 no goals
  · obtain ⟨U, hU, hU', hy, hx⟩ := exists_clopen_lower_of_not_le h
    -- ⊢ ∃ U, IsClopen U ∧ (IsUpperSet U ∨ IsLowerSet U) ∧ x ∈ U ∧ ¬y ∈ U
    exact ⟨U, hU, Or.inr hU', hx, hy⟩
    -- 🎉 no goals
#align exists_clopen_upper_or_lower_of_ne exists_clopen_upper_or_lower_of_ne

-- See note [lower instance priority]
instance (priority := 100) PriestleySpace.toT2Space : T2Space α :=
  ⟨fun _ _ h ↦
    let ⟨U, hU, _, hx, hy⟩ := exists_clopen_upper_or_lower_of_ne h
    ⟨U, Uᶜ, hU.isOpen, hU.compl.isOpen, hx, hy, disjoint_compl_right⟩⟩
#align priestley_space.to_t2_space PriestleySpace.toT2Space

end PartialOrder

/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Contrapose
import Mathlib.Order.Bounds.Defs

/-!
# Cofinal sets

A set `s` in an ordered type `α` is cofinal when for every `a : α` there exists an element of `s`
greater or equal to it. This file provides a basic API for the `IsCofinal` predicate.

For the cofinality of a set as a cardinal, see `Mathlib.SetTheory.Cardinal.Cofinality`.

## TODO

- Define `Order.cof` in terms of `Cofinal`.
-/

variable {α : Type*}

section LE
variable [LE α]

theorem isCofinal_of_isEmpty [IsEmpty α] (s : Set α) : IsCofinal s :=
  fun a ↦ isEmptyElim a

theorem isCofinal_empty_iff : IsCofinal (∅ : Set α) ↔ IsEmpty α := by
  refine ⟨fun h ↦ ⟨fun a ↦ ?_⟩, fun h ↦ isCofinal_of_isEmpty _⟩
  simpa using h a

theorem isCofinal_top [OrderTop α] : IsCofinal {(⊤ : α)} :=
  fun _ ↦ ⟨⊤, Set.mem_singleton _, le_top⟩

theorem isCofinal_mono {s t : Set α} (h : s ⊆ t) (hs : IsCofinal s) : IsCofinal t := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩

end LE

section Preorder
variable [Preorder α]

theorem isCofinal_univ : IsCofinal (@Set.univ α) :=
  fun a ↦ ⟨a, ⟨⟩, le_rfl⟩

/-- A cofinal subset of a cofinal subset is cofinal. -/
theorem IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal t) :
    IsCofinal (Subtype.val '' t) := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  obtain ⟨c, hc, hc'⟩ := ht ⟨b, hb⟩
  exact ⟨c, Set.mem_image_of_mem _ hc, hb'.trans hc'⟩

end Preorder

section PartialOrder
variable [PartialOrder α]

theorem IsCofinal.isMax_mem {s : Set α} {a : α} (ha : IsMax a) (hs : IsCofinal s) : a ∈ s := by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb

theorem IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCofinal s) : ⊤ ∈ s :=
  hs.isMax_mem isMax_top

@[simp]
theorem isCofinal_iff_of_orderTop [OrderTop α] {s : Set α} : IsCofinal s ↔ ⊤ ∈ s :=
  ⟨IsCofinal.top_mem, fun hs _ ↦ ⟨⊤, hs, le_top⟩⟩

end PartialOrder

section LinearOrder
variable [LinearOrder α]

theorem not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ ∃ x, ∀ y ∈ s, y < x := by
  simp [IsCofinal]

theorem bddAbove_of_not_isCofinal {s : Set α} (h : ¬ IsCofinal s) : BddAbove s := by
  rw [not_isCofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy ↦ (h y hy).le⟩

theorem isCofinal_of_not_bddAbove {s : Set α} (h : ¬ BddAbove s) : IsCofinal s := by
  contrapose! h
  exact bddAbove_of_not_isCofinal h

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
theorem not_isCofinal_iff_bddAbove [NoMaxOrder α] {s : Set α} : ¬ IsCofinal s ↔ BddAbove s := by
  use bddAbove_of_not_isCofinal
  rw [not_isCofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy ↦ (h hy).trans_lt hz⟩

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
theorem not_bddAbove_iff_isCofinal [NoMaxOrder α] {s : Set α} : ¬ BddAbove s ↔ IsCofinal s :=
  not_iff_comm.1 not_isCofinal_iff_bddAbove

end LinearOrder

/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.Bounds.Basic

/-!
# Cofinal sets

A set `s` is cofinal when for every `a` there exists an element of `s` greater or equal to it. This
file provides a basic API for the `Cofinal` predicate.

For the cofinality of a set as a cardinal, see `Mathlib.SetTheory.Cardinal.Cofinality`.

## TODO

Define `Order.cof` in terms of `Cofinal`.
-/

variable {α : Type*}

section LE
variable [LE α]

theorem cofinal_of_isEmpty [IsEmpty α] (s : Set α) : Cofinal s :=
  fun a ↦ isEmptyElim a

theorem cofinal_empty_iff : Cofinal (∅ : Set α) ↔ IsEmpty α := by
  refine ⟨fun h ↦ ⟨fun a ↦ ?_⟩, fun h ↦ cofinal_of_isEmpty _⟩
  simpa using h a

theorem cofinal_top [OrderTop α] : Cofinal {(⊤ : α)} :=
  fun _ ↦ ⟨⊤, Set.mem_singleton _, le_top⟩

theorem cofinal_mono {s t : Set α} (h : s ⊆ t) (hs : Cofinal s) : Cofinal t := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩

end LE

section Preorder
variable [Preorder α]

theorem cofinal_univ : Cofinal (@Set.univ α) := by
  intro a
  exact ⟨a, ⟨⟩, le_rfl⟩

/-- A cofinal subset of a cofinal subset is cofinal. -/
theorem cofinal_trans {s : Set α} {t : Set s} (hs : Cofinal s) (ht : Cofinal t) :
    Cofinal (Subtype.val '' t) := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  obtain ⟨c, hc, hc'⟩ := ht ⟨b, hb⟩
  exact ⟨c, Set.mem_image_of_mem _ hc, hb'.trans hc'⟩

end Preorder

section PartialOrder
variable [PartialOrder α]

theorem mem_cofinal_of_isMax {s : Set α} {a : α} (hs : Cofinal s) (ha : IsMax a) : a ∈ s := by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb

theorem top_mem_cofinal [OrderTop α] {s : Set α} (hs : Cofinal s) : ⊤ ∈ s :=
  mem_cofinal_of_isMax hs isMax_top

@[simp]
theorem cofinal_iff_of_orderTop [OrderTop α] {s : Set α} : Cofinal s ↔ ⊤ ∈ s :=
  ⟨top_mem_cofinal, fun hs _ ↦ ⟨⊤, hs, le_top⟩⟩

end PartialOrder

section LinearOrder
variable [LinearOrder α]

theorem not_cofinal_iff {s : Set α} : ¬ Cofinal s ↔ ∃ x, ∀ y ∈ s, y < x := by
  simp [Cofinal]

theorem bddAbove_of_not_cofinal {s : Set α} (h : ¬ Cofinal s) : BddAbove s := by
  rw [not_cofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy ↦ (h y hy).le⟩

theorem cofinal_of_not_bddAbove {s : Set α} (h : ¬ BddAbove s) : Cofinal s := by
  contrapose! h
  exact bddAbove_of_not_cofinal h

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
theorem not_cofinal_iff_bddAbove [NoMaxOrder α] {s : Set α} : ¬ Cofinal s ↔ BddAbove s := by
  use bddAbove_of_not_cofinal
  rw [not_cofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy ↦ (h hy).trans_lt hz⟩

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
theorem not_bddAbove_iff_cofinal [NoMaxOrder α] {s : Set α} : ¬ BddAbove s ↔ Cofinal s :=
  not_iff_comm.1 not_cofinal_iff_bddAbove

end LinearOrder

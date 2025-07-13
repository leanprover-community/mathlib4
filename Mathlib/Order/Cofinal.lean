/-
Copyright (c) 2024 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.WellFounded

/-!
# Cofinal sets

A set `s` in an ordered type `α` is cofinal when for every `a : α` there exists an element of `s`
greater or equal to it. This file provides a basic API for the `IsCofinal` predicate.

For the cofinality of a set as a cardinal, see `Mathlib/SetTheory/Cardinal/Cofinality.lean`.

## TODO

- Define `Order.cof` in terms of `Cofinal`.
- Deprecate `Order.Cofinal` in favor of this predicate.
-/

variable {α β : Type*}

section LE
variable [LE α]

theorem IsCofinal.of_isEmpty [IsEmpty α] (s : Set α) : IsCofinal s :=
  fun a ↦ isEmptyElim a

theorem isCofinal_empty_iff : IsCofinal (∅ : Set α) ↔ IsEmpty α := by
  refine ⟨fun h ↦ ⟨fun a ↦ ?_⟩, fun h ↦ .of_isEmpty _⟩
  simpa using h a

theorem IsCofinal.singleton_top [OrderTop α] : IsCofinal {(⊤ : α)} :=
  fun _ ↦ ⟨⊤, Set.mem_singleton _, le_top⟩

theorem IsCofinal.mono {s t : Set α} (h : s ⊆ t) (hs : IsCofinal s) : IsCofinal t := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  exact ⟨b, h hb, hb'⟩

end LE

section Preorder
variable [Preorder α]

theorem IsCofinal.univ : IsCofinal (@Set.univ α) :=
  fun a ↦ ⟨a, ⟨⟩, le_rfl⟩

instance : Inhabited {s : Set α // IsCofinal s} :=
  ⟨_, .univ⟩

/-- A cofinal subset of a cofinal subset is cofinal. -/
theorem IsCofinal.trans {s : Set α} {t : Set s} (hs : IsCofinal s) (ht : IsCofinal t) :
    IsCofinal (Subtype.val '' t) := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs a
  obtain ⟨c, hc, hc'⟩ := ht ⟨b, hb⟩
  exact ⟨c, Set.mem_image_of_mem _ hc, hb'.trans hc'⟩

theorem GaloisConnection.map_cofinal [Preorder β] {f : β → α} {g : α → β}
    (h : GaloisConnection f g) {s : Set α} (hs : IsCofinal s) : IsCofinal (g '' s) := by
  intro a
  obtain ⟨b, hb, hb'⟩ := hs (f a)
  exact ⟨g b, Set.mem_image_of_mem _ hb, h.le_iff_le.1 hb'⟩

theorem OrderIso.map_cofinal [Preorder β] (e : α ≃o β) {s : Set α} (hs : IsCofinal s) :
    IsCofinal (e '' s) :=
  e.symm.to_galoisConnection.map_cofinal hs

end Preorder

section PartialOrder
variable [PartialOrder α]

theorem IsCofinal.mem_of_isMax {s : Set α} {a : α} (ha : IsMax a) (hs : IsCofinal s) : a ∈ s := by
  obtain ⟨b, hb, hb'⟩ := hs a
  rwa [ha.eq_of_ge hb'] at hb

theorem IsCofinal.top_mem [OrderTop α] {s : Set α} (hs : IsCofinal s) : ⊤ ∈ s :=
  hs.mem_of_isMax isMax_top

@[simp]
theorem isCofinal_iff_top_mem [OrderTop α] {s : Set α} : IsCofinal s ↔ ⊤ ∈ s :=
  ⟨IsCofinal.top_mem, fun hs _ ↦ ⟨⊤, hs, le_top⟩⟩

end PartialOrder

section LinearOrder
variable [LinearOrder α]

theorem not_isCofinal_iff {s : Set α} : ¬ IsCofinal s ↔ ∃ x, ∀ y ∈ s, y < x := by
  simp [IsCofinal]

theorem BddAbove.of_not_isCofinal {s : Set α} (h : ¬ IsCofinal s) : BddAbove s := by
  rw [not_isCofinal_iff] at h
  obtain ⟨x, h⟩ := h
  exact ⟨x, fun y hy ↦ (h y hy).le⟩

theorem IsCofinal.of_not_bddAbove {s : Set α} (h : ¬ BddAbove s) : IsCofinal s := by
  contrapose! h
  exact .of_not_isCofinal h

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
theorem not_isCofinal_iff_bddAbove [NoMaxOrder α] {s : Set α} : ¬ IsCofinal s ↔ BddAbove s := by
  use .of_not_isCofinal
  rw [not_isCofinal_iff]
  rintro ⟨x, h⟩
  obtain ⟨z, hz⟩ := exists_gt x
  exact ⟨z, fun y hy ↦ (h hy).trans_lt hz⟩

/-- In a linear order with no maximum, cofinal sets are the same as unbounded sets. -/
theorem not_bddAbove_iff_isCofinal [NoMaxOrder α] {s : Set α} : ¬ BddAbove s ↔ IsCofinal s :=
  not_iff_comm.1 not_isCofinal_iff_bddAbove

/-- The set of "records" (the smallest inputs yielding the highest values) with respect to a
well-ordering of `α` is a cofinal set. -/
theorem isCofinal_setOf_imp_lt (r : α → α → Prop) [h : IsWellFounded α r] :
    IsCofinal { a | ∀ b, r b a → b < a } := by
  intro a
  obtain ⟨b, hb, hb'⟩ := h.wf.has_min (Set.Ici a) Set.nonempty_Ici
  refine ⟨b, fun c hc ↦ ?_, hb⟩
  by_contra! hc'
  exact hb' c (hb.trans hc') hc

end LinearOrder

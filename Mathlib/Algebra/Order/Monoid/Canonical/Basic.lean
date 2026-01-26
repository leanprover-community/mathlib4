/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Algebra.Order.Monoid.Canonical.Defs
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Extra lemmas about canonically ordered monoids
-/

public section

namespace Finset
variable {ι α : Type*} [AddCommMonoid α] [LinearOrder α] [OrderBot α] [CanonicallyOrderedAdd α]
  {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']
@[simp] lemma sup'_eq_zero (hs) : s.sup' hs f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [sup'_eq_sup]

end Finset

namespace Set
variable {α : Type*} [AddCommMonoid α] [PartialOrder α] [CanonicallyOrderedAdd α]
  [Sub α] [OrderedSub α] {β : Type*} {f : α → β} {k : α}

theorem range_add_eq_image_Ici : range (fun x ↦ f (x + k)) = f '' Ici k :=
  Set.ext fun x ↦ ⟨fun ⟨y, hfy⟩ ↦ ⟨y + k, self_le_add_left k y, hfy⟩,
    fun ⟨y, hy, hfy⟩ ↦ ⟨y - k, by simpa [tsub_add_cancel_of_le hy] using hfy⟩⟩

end Set

section LinearOrder
variable {α : Type*} [LinearOrder α] {P : α → Prop} {a b c : α}

section Add
variable [Add α] [CanonicallyOrderedAdd α]

theorem lt_add_iff_lt_left_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < b ∨ ∃ d < c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

theorem forall_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∀ a < b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

theorem exists_lt_add_iff_lt_left [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∃ a < b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ d < c, P (b + d)) := by
  simp_rw [lt_add_iff_lt_left_or_exists_lt]
  aesop

theorem le_add_iff_lt_left_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a ≤ b + c ↔ a < b ∨ ∃ d ≤ c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a ≤ b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

theorem forall_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (∀ a ≤ b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ d ≤ c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

theorem exists_le_add_iff_le_left [AddLeftMono α] [IsLeftCancelAdd α] :
    (∃ a ≤ b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ d ≤ c, P (b + d)) := by
  simp_rw [le_add_iff_lt_left_or_exists_le]
  aesop

end Add

section AddCommMagma
variable [AddCommMagma α] [CanonicallyOrderedAdd α]

theorem lt_add_iff_lt_right_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    a < b + c ↔ a < c ∨ ∃ d < b, a = d + c := by
  rw [add_comm, lt_add_iff_lt_left_or_exists_lt]
  simp_rw [add_comm]

theorem forall_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∀ a < b + c, P a) ↔ (∀ a < c, P a) ∧ (∀ d < b, P (d + c)) := by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

theorem exists_lt_add_iff_lt_right [AddLeftReflectLT α] [IsLeftCancelAdd α] :
    (∃ a < b + c, P a) ↔ (∃ a < c, P a) ∨ (∃ d < b, P (d + c)) := by
  simp_rw [lt_add_iff_lt_right_or_exists_lt]
  aesop

theorem le_add_iff_lt_right_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] :
    a ≤ b + c ↔ a < c ∨ ∃ d ≤ b, a = d + c := by
  rw [add_comm, le_add_iff_lt_left_or_exists_le]
  simp_rw [add_comm]

theorem forall_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (∀ a ≤ b + c, P a) ↔ (∀ a < c, P a) ∧ (∀ d ≤ b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

theorem exists_le_add_iff_le_right [AddLeftMono α] [IsLeftCancelAdd α] :
    (∃ a ≤ b + c, P a) ↔ (∃ a < c, P a) ∨ (∃ d ≤ b, P (d + c)) := by
  simp_rw [le_add_iff_lt_right_or_exists_le]
  aesop

end AddCommMagma
end LinearOrder

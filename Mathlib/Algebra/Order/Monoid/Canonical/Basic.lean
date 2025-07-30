/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Extra lemmas about canonically ordered monoids
-/

namespace Finset
variable {ι α : Type*} [AddCommMonoid α] [LinearOrder α] [OrderBot α] [CanonicallyOrderedAdd α]
  {s : Finset ι} {f : ι → α}

@[simp] lemma sup_eq_zero : s.sup f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [← bot_eq_zero']
@[simp] lemma sup'_eq_zero (hs) : s.sup' hs f = 0 ↔ ∀ i ∈ s, f i = 0 := by simp [sup'_eq_sup]

end Finset

section LinearOrder
variable {α : Type*} [Add α] [LinearOrder α] [CanonicallyOrderedAdd α]

theorem lt_add_iff_lt_or_exists_lt [AddLeftReflectLT α] [IsLeftCancelAdd α] {a b c : α} :
    a < b + c ↔ a < b ∨ ∃ d < c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a < b + c := h.trans_le (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

theorem forall_lt_add [AddLeftReflectLT α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∀ a < b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ a < c, P (b + a)) := by
  simp_rw [lt_add_iff_lt_or_exists_lt]
  aesop

theorem exists_lt_add [AddLeftReflectLT α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∃ a < b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ a < c, P (b + a)) := by
  simp_rw [lt_add_iff_lt_or_exists_lt]
  aesop

theorem le_add_iff_lt_or_exists_le [AddLeftMono α] [IsLeftCancelAdd α] {a b c : α} :
    a ≤ b + c ↔ a < b ∨ ∃ d ≤ c, a = b + d := by
  obtain h | h := lt_or_ge a b
  · have : a ≤ b + c := h.le.trans (le_self_add ..)
    tauto
  · obtain ⟨a, rfl⟩ := exists_add_of_le h
    simp

theorem forall_le_add [AddLeftMono α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∀ a ≤ b + c, P a) ↔ (∀ a < b, P a) ∧ (∀ a ≤ c, P (b + a)) := by
  simp_rw [le_add_iff_lt_or_exists_le]
  aesop

theorem exists_le_add [AddLeftMono α] [IsLeftCancelAdd α] {b c : α} {P : α → Prop} :
    (∃ a ≤ b + c, P a) ↔ (∃ a < b, P a) ∨ (∃ a ≤ c, P (b + a)) := by
  simp_rw [le_add_iff_lt_or_exists_le]
  aesop

end LinearOrder

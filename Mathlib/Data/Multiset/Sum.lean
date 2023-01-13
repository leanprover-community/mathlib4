/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies

! This file was ported from Lean 3 source module data.multiset.sum
! leanprover-community/mathlib commit 9003f28797c0664a49e4179487267c494477d853
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Multiset.Nodup

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `multiset (α ⊕ β)`. Beware not to confuse
with the `multiset.sum` operation which computes the additive sum.

## Main declarations

* `multiset.disj_sum`: `s.disj_sum t` is the disjoint sum of `s` and `t`.
-/


open Sum

namespace Multiset

variable {α β : Type _} (s : Multiset α) (t : Multiset β)

/-- Disjoint sum of multisets. -/
def disjSum : Multiset (Sum α β) :=
  s.map inl + t.map inr
#align multiset.disj_sum Multiset.disjSum

@[simp]
theorem zero_disj_sum : (0 : Multiset α).disjSum t = t.map inr :=
  zero_add _
#align multiset.zero_disj_sum Multiset.zero_disj_sum

@[simp]
theorem disj_sum_zero : s.disjSum (0 : Multiset β) = s.map inl :=
  add_zero _
#align multiset.disj_sum_zero Multiset.disj_sum_zero

@[simp]
theorem card_disj_sum : (s.disjSum t).card = s.card + t.card := by
  rw [disj_sum, card_add, card_map, card_map]
#align multiset.card_disj_sum Multiset.card_disj_sum

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : Sum α β}

theorem mem_disj_sum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x := by
  simp_rw [disj_sum, mem_add, mem_map]
#align multiset.mem_disj_sum Multiset.mem_disj_sum

@[simp]
theorem inl_mem_disj_sum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  by
  rw [mem_disj_sum, or_iff_left]
  simp only [exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb
#align multiset.inl_mem_disj_sum Multiset.inl_mem_disj_sum

@[simp]
theorem inr_mem_disj_sum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  by
  rw [mem_disj_sum, or_iff_right]
  simp only [exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha
#align multiset.inr_mem_disj_sum Multiset.inr_mem_disj_sum

theorem disj_sum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disjSum t₁ ≤ s₂.disjSum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)
#align multiset.disj_sum_mono Multiset.disj_sum_mono

theorem disj_sum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disjSum t :=
  fun s₁ s₂ hs => add_le_add_right (map_le_map hs) _
#align multiset.disj_sum_mono_left Multiset.disj_sum_mono_left

theorem disj_sum_mono_right (s : Multiset α) :
    Monotone (s.disjSum : Multiset β → Multiset (Sum α β)) := fun t₁ t₂ ht =>
  add_le_add_left (map_le_map ht) _
#align multiset.disj_sum_mono_right Multiset.disj_sum_mono_right

theorem disj_sum_lt_disj_sum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)
#align multiset.disj_sum_lt_disj_sum_of_lt_of_le Multiset.disj_sum_lt_disj_sum_of_lt_of_le

theorem disj_sum_lt_disj_sum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)
#align multiset.disj_sum_lt_disj_sum_of_le_of_lt Multiset.disj_sum_lt_disj_sum_of_le_of_lt

theorem disj_sum_strict_mono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disjSum t :=
  fun s₁ s₂ hs => disj_sum_lt_disj_sum_of_lt_of_le hs le_rfl
#align multiset.disj_sum_strict_mono_left Multiset.disj_sum_strict_mono_left

theorem disj_sum_strict_mono_right (s : Multiset α) :
    StrictMono (s.disjSum : Multiset β → Multiset (Sum α β)) := fun s₁ s₂ =>
  disj_sum_lt_disj_sum_of_le_of_lt le_rfl
#align multiset.disj_sum_strict_mono_right Multiset.disj_sum_strict_mono_right

protected theorem Nodup.disj_sum (hs : s.Nodup) (ht : t.Nodup) : (s.disjSum t).Nodup :=
  by
  refine' ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 fun x hs ht => _
  rw [Multiset.mem_map] at hs ht
  obtain ⟨a, _, rfl⟩ := hs
  obtain ⟨b, _, h⟩ := ht
  exact inr_ne_inl h
#align multiset.nodup.disj_sum Multiset.Nodup.disj_sum

end Multiset


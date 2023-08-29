/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Multiset.Nodup

#align_import data.multiset.sum from "leanprover-community/mathlib"@"9003f28797c0664a49e4179487267c494477d853"

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `Multiset (α ⊕ β)`. Beware not to confuse
with the `Multiset.sum` operation which computes the additive sum.

## Main declarations

* `Multiset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
-/


open Sum

namespace Multiset

variable {α β : Type*} (s : Multiset α) (t : Multiset β)

/-- Disjoint sum of multisets. -/
def disjSum : Multiset (Sum α β) :=
  s.map inl + t.map inr
#align multiset.disj_sum Multiset.disjSum

@[simp]
theorem zero_disjSum : (0 : Multiset α).disjSum t = t.map inr :=
  zero_add _
#align multiset.zero_disj_sum Multiset.zero_disjSum

@[simp]
theorem disjSum_zero : s.disjSum (0 : Multiset β) = s.map inl :=
  add_zero _
#align multiset.disj_sum_zero Multiset.disjSum_zero

@[simp]
theorem card_disjSum : Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t := by
  rw [disjSum, card_add, card_map, card_map]
  -- 🎉 no goals
#align multiset.card_disj_sum Multiset.card_disjSum

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : Sum α β}

theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x := by
  simp_rw [disjSum, mem_add, mem_map]
  -- 🎉 no goals
#align multiset.mem_disj_sum Multiset.mem_disjSum

@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s := by
  rw [mem_disjSum, or_iff_left]
  -- ⊢ (∃ a_1, a_1 ∈ s ∧ inl a_1 = inl a) ↔ a ∈ s
  -- Porting note: Previous code for L62 was: simp only [exists_eq_right]
  simp only [inl.injEq, exists_eq_right]
  -- ⊢ ¬∃ b, b ∈ t ∧ inr b = inl a
  rintro ⟨b, _, hb⟩
  -- ⊢ False
  exact inr_ne_inl hb
  -- 🎉 no goals
#align multiset.inl_mem_disj_sum Multiset.inl_mem_disjSum

@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t := by
  rw [mem_disjSum, or_iff_right]
  -- ⊢ (∃ b_1, b_1 ∈ t ∧ inr b_1 = inr b) ↔ b ∈ t
  -- Porting note: Previous code for L72 was: simp only [exists_eq_right]
  simp only [inr.injEq, exists_eq_right]
  -- ⊢ ¬∃ a, a ∈ s ∧ inl a = inr b
  rintro ⟨a, _, ha⟩
  -- ⊢ False
  exact inl_ne_inr ha
  -- 🎉 no goals
#align multiset.inr_mem_disj_sum Multiset.inr_mem_disjSum

theorem disjSum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disjSum t₁ ≤ s₂.disjSum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)
#align multiset.disj_sum_mono Multiset.disjSum_mono

theorem disjSum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => add_le_add_right (map_le_map hs) _
#align multiset.disj_sum_mono_left Multiset.disjSum_mono_left

theorem disjSum_mono_right (s : Multiset α) :
    Monotone (s.disjSum : Multiset β → Multiset (Sum α β)) := fun _ _ ht =>
  add_le_add_left (map_le_map ht) _
#align multiset.disj_sum_mono_right Multiset.disjSum_mono_right

theorem disjSum_lt_disjSum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)
#align multiset.disj_sum_lt_disj_sum_of_lt_of_le Multiset.disjSum_lt_disjSum_of_lt_of_le

theorem disjSum_lt_disjSum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)
#align multiset.disj_sum_lt_disj_sum_of_le_of_lt Multiset.disjSum_lt_disjSum_of_le_of_lt

theorem disjSum_strictMono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl
#align multiset.disj_sum_strict_mono_left Multiset.disjSum_strictMono_left

theorem disjSum_strictMono_right (s : Multiset α) :
    StrictMono (s.disjSum : Multiset β → Multiset (Sum α β)) := fun _ _ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl
#align multiset.disj_sum_strict_mono_right Multiset.disjSum_strictMono_right

protected theorem Nodup.disjSum (hs : s.Nodup) (ht : t.Nodup) : (s.disjSum t).Nodup := by
  refine' ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 fun x hs ht => _
  -- ⊢ False
  rw [Multiset.mem_map] at hs ht
  -- ⊢ False
  obtain ⟨a, _, rfl⟩ := hs
  -- ⊢ False
  obtain ⟨b, _, h⟩ := ht
  -- ⊢ False
  exact inr_ne_inl h
  -- 🎉 no goals
#align multiset.nodup.disj_sum Multiset.Nodup.disjSum

end Multiset

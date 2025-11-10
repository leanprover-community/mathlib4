/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Algebra.Order.Group.Multiset

/-!
# Disjoint sum of multisets

This file defines the disjoint sum of two multisets as `Multiset (α ⊕ β)`. Beware not to confuse
with the `Multiset.sum` operation which computes the additive sum.

## Main declarations

* `Multiset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
-/


open Sum

namespace Multiset

variable {α β γ : Type*} (s : Multiset α) (t : Multiset β)

/-- Disjoint sum of multisets. -/
def disjSum : Multiset (α ⊕ β) :=
  s.map inl + t.map inr

@[simp]
theorem zero_disjSum : (0 : Multiset α).disjSum t = t.map inr :=
  Multiset.zero_add _

@[simp]
theorem disjSum_zero : s.disjSum (0 : Multiset β) = s.map inl :=
  Multiset.add_zero _

@[simp]
theorem card_disjSum : Multiset.card (s.disjSum t) = Multiset.card s + Multiset.card t := by
  rw [disjSum, card_add, card_map, card_map]

variable {s t} {s₁ s₂ : Multiset α} {t₁ t₂ : Multiset β} {a : α} {b : β} {x : α ⊕ β}

theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x := by
  simp_rw [disjSum, mem_add, mem_map]

@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s := by
  rw [mem_disjSum, or_iff_left]
  · simp only [inl.injEq, exists_eq_right]
  rintro ⟨b, _, hb⟩
  exact inr_ne_inl hb

@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t := by
  rw [mem_disjSum, or_iff_right]
  · simp only [inr.injEq, exists_eq_right]
  rintro ⟨a, _, ha⟩
  exact inl_ne_inr ha

theorem disjSum_mono (hs : s₁ ≤ s₂) (ht : t₁ ≤ t₂) : s₁.disjSum t₁ ≤ s₂.disjSum t₂ :=
  add_le_add (map_le_map hs) (map_le_map ht)

theorem disjSum_mono_left (t : Multiset β) : Monotone fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => Multiset.add_le_add_right (map_le_map hs)

theorem disjSum_mono_right (s : Multiset α) :
    Monotone (s.disjSum : Multiset β → Multiset (α ⊕ β)) := fun _ _ ht =>
  Multiset.add_le_add_left (map_le_map ht)

theorem disjSum_lt_disjSum_of_lt_of_le (hs : s₁ < s₂) (ht : t₁ ≤ t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_lt_of_le (map_lt_map hs) (map_le_map ht)

theorem disjSum_lt_disjSum_of_le_of_lt (hs : s₁ ≤ s₂) (ht : t₁ < t₂) :
    s₁.disjSum t₁ < s₂.disjSum t₂ :=
  add_lt_add_of_le_of_lt (map_le_map hs) (map_lt_map ht)

theorem disjSum_strictMono_left (t : Multiset β) : StrictMono fun s : Multiset α => s.disjSum t :=
  fun _ _ hs => disjSum_lt_disjSum_of_lt_of_le hs le_rfl

theorem disjSum_strictMono_right (s : Multiset α) :
    StrictMono (s.disjSum : Multiset β → Multiset (α ⊕ β)) := fun _ _ =>
  disjSum_lt_disjSum_of_le_of_lt le_rfl

protected theorem Nodup.disjSum (hs : s.Nodup) (ht : t.Nodup) : (s.disjSum t).Nodup := by
  refine ((hs.map inl_injective).add_iff <| ht.map inr_injective).2 ?_
  rw [disjoint_map_map]
  exact fun _ _ _ _ ↦ inr_ne_inl.symm

theorem map_disjSum (f : α ⊕ β → γ) :
    (s.disjSum t).map f = s.map (f <| .inl ·) + t.map (f <| .inr ·) := by
  simp_rw [disjSum, map_add, map_map, Function.comp_def]

end Multiset

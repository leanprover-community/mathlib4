/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Finset.Card

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `Finset (α ⊕ β)`. Beware not to confuse with
the `Finset.sum` operation which computes the additive sum.

## Main declarations

* `Finset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
-/


open Function Multiset Sum

namespace Finset

variable {α β : Type*} (s : Finset α) (t : Finset β)

/-- Disjoint sum of finsets. -/
def disjSum : Finset (α ⊕ β) :=
  ⟨s.1.disjSum t.1, s.2.disjSum t.2⟩

@[simp]
theorem val_disjSum : (s.disjSum t).1 = s.1.disjSum t.1 :=
  rfl

@[simp]
theorem empty_disjSum : (∅ : Finset α).disjSum t = t.map Embedding.inr :=
  val_inj.1 <| Multiset.zero_disjSum _

@[simp]
theorem disjSum_empty : s.disjSum (∅ : Finset β) = s.map Embedding.inl :=
  val_inj.1 <| Multiset.disjSum_zero _

@[simp]
theorem card_disjSum : (s.disjSum t).card = s.card + t.card :=
  Multiset.card_disjSum _ _

theorem disjoint_map_inl_map_inr : Disjoint (s.map Embedding.inl) (t.map Embedding.inr) := by
  simp_rw [disjoint_left, mem_map]
  rintro x ⟨a, _, rfl⟩ ⟨b, _, ⟨⟩⟩

@[simp]
theorem map_inl_disjUnion_map_inr :
    (s.map Embedding.inl).disjUnion (t.map Embedding.inr) (disjoint_map_inl_map_inr _ _) =
      s.disjSum t :=
  rfl

variable {s t} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} {a : α} {b : β} {x : α ⊕ β}

theorem mem_disjSum : x ∈ s.disjSum t ↔ (∃ a, a ∈ s ∧ inl a = x) ∨ ∃ b, b ∈ t ∧ inr b = x :=
  Multiset.mem_disjSum

@[simp]
theorem inl_mem_disjSum : inl a ∈ s.disjSum t ↔ a ∈ s :=
  Multiset.inl_mem_disjSum

@[simp]
theorem inr_mem_disjSum : inr b ∈ s.disjSum t ↔ b ∈ t :=
  Multiset.inr_mem_disjSum

@[simp]
theorem disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅ := by simp [ext_iff]

theorem disjSum_mono (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : s₁.disjSum t₁ ⊆ s₂.disjSum t₂ :=
  val_le_iff.1 <| Multiset.disjSum_mono (val_le_iff.2 hs) (val_le_iff.2 ht)

theorem disjSum_mono_left (t : Finset β) : Monotone fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_mono hs Subset.rfl

theorem disjSum_mono_right (s : Finset α) : Monotone (s.disjSum : Finset β → Finset (α ⊕ β)) :=
  fun _ _ => disjSum_mono Subset.rfl

theorem disjSum_ssubset_disjSum_of_ssubset_of_subset (hs : s₁ ⊂ s₂) (ht : t₁ ⊆ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_lt_of_le (val_lt_iff.2 hs) (val_le_iff.2 ht)

theorem disjSum_ssubset_disjSum_of_subset_of_ssubset (hs : s₁ ⊆ s₂) (ht : t₁ ⊂ t₂) :
    s₁.disjSum t₁ ⊂ s₂.disjSum t₂ :=
  val_lt_iff.1 <| disjSum_lt_disjSum_of_le_of_lt (val_le_iff.2 hs) (val_lt_iff.2 ht)

theorem disjSum_strictMono_left (t : Finset β) : StrictMono fun s : Finset α => s.disjSum t :=
  fun _ _ hs => disjSum_ssubset_disjSum_of_ssubset_of_subset hs Subset.rfl

theorem disj_sum_strictMono_right (s : Finset α) :
    StrictMono (s.disjSum : Finset β → Finset (α ⊕ β)) := fun _ _ =>
  disjSum_ssubset_disjSum_of_subset_of_ssubset Subset.rfl

end Finset

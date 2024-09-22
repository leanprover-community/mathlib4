/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import Mathlib.Data.Multiset.Sum
import Mathlib.Data.Finset.Card

/-!
# Disjoint sum of finsets

This file defines the disjoint sum of two finsets as `Finset (α ⊕ β)`. Beware not to confuse with
the `Finset.sum` operation which computes the additive sum.

## Main declarations

* `Finset.disjSum`: `s.disjSum t` is the disjoint sum of `s` and `t`.
* `Finset.toLeft`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `α`.
* `Finset.toRight`: Given a finset of elements `α ⊕ β`, extracts all the elements of the form `β`.
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
theorem disjSum_eq_empty : s.disjSum t = ∅ ↔ s = ∅ ∧ t = ∅ := by simp [Finset.ext_iff]

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

@[simp] lemma disjSum_inj {α β : Type*} {s₁ s₂ : Finset α} {t₁ t₂ : Finset β} :
    s₁.disjSum t₁ = s₂.disjSum t₂ ↔ s₁ = s₂ ∧ t₁ = t₂ := by
  simp [Finset.ext_iff]

lemma Injective2_disjSum {α β : Type*} : Function.Injective2 (@disjSum α β) :=
  fun _ _ _ _ => by simp [Finset.ext_iff]

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `α`. This
forms a quasi-inverse to `disjSum`, in that it recovers its left input.
-/
def toLeft (s : Finset (α ⊕ β)) : Finset α :=
  s.disjiUnion (Sum.elim singleton (fun _ => ∅)) <| by
    simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, eq_comm]

/--
Given a finset of elements `α ⊕ β`, extract all the elements of the form `β`. This
forms a quasi-inverse to `disjSum`, in that it recovers its right input.
-/
def toRight (s : Finset (α ⊕ β)) : Finset β :=
  s.disjiUnion (Sum.elim (fun _ => ∅) singleton) <| by
    simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, eq_comm]

@[simp] lemma mem_toLeft {s : Finset (α ⊕ β)} {x : α} : x ∈ s.toLeft ↔ inl x ∈ s := by
  simp [toLeft]

@[simp] lemma mem_toRight {s : Finset (α ⊕ β)} {x : β} : x ∈ s.toRight ↔ inr x ∈ s := by
  simp [toRight]

@[gcongr]
lemma toLeft_subset_toLeft {s t : Finset (α ⊕ β)} : s ⊆ t → s.toLeft ⊆ t.toLeft :=
  fun h _ => by simpa only [mem_toLeft] using @h _

@[gcongr]
lemma toRight_subset_toRight {s t : Finset (α ⊕ β)} : s ⊆ t → s.toRight ⊆ t.toRight :=
  fun h _ => by simpa only [mem_toRight] using @h _

lemma toLeft_monotone : Monotone (@toLeft α β) := fun _ _ => toLeft_subset_toLeft
lemma toRight_monotone : Monotone (@toRight α β) := fun _ _ => toRight_subset_toRight

lemma toLeft_disjSum_toRight {s : Finset (α ⊕ β)} : s.toLeft.disjSum s.toRight = s := by
  ext (x | x) <;> simp

lemma card_toLeft_add_card_toRight {s : Finset (α ⊕ β)} :
    s.toLeft.card + s.toRight.card = s.card := by
  rw [← card_disjSum, toLeft_disjSum_toRight]

lemma card_toLeft_le {s : Finset (α ⊕ β)} : s.toLeft.card ≤ s.card :=
  (Nat.le_add_right _ _).trans_eq card_toLeft_add_card_toRight

lemma card_toRight_le {s : Finset (α ⊕ β)} : s.toRight.card ≤ s.card :=
  (Nat.le_add_left _ _).trans_eq card_toLeft_add_card_toRight

@[simp] lemma toLeft_disjSum : (s.disjSum t).toLeft = s := by ext x; simp

@[simp] lemma toRight_disjSum : (s.disjSum t).toRight = t := by ext x; simp

lemma disjSum_eq_iff {u : Finset (α ⊕ β)} : s.disjSum t = u ↔ s = u.toLeft ∧ t = u.toRight :=
  ⟨fun h => by simp [← h], fun h => by simp [h, toLeft_disjSum_toRight]⟩

lemma eq_disjSum_iff {u : Finset (α ⊕ β)} : u = s.disjSum t ↔ u.toLeft = s ∧ u.toRight = t :=
  ⟨fun h => by simp [h], fun h => by simp [← h, toLeft_disjSum_toRight]⟩

variable [DecidableEq α] [DecidableEq β] {s t : Finset (α ⊕ β)}

@[simp] lemma toLeft_insert_inl : (insert (inl a) s).toLeft = insert a s.toLeft := by ext y; simp
@[simp] lemma toLeft_insert_inr : (insert (inr b) s).toLeft = s.toLeft := by ext y; simp
@[simp] lemma toRight_insert_inl : (insert (inl a) s).toRight = s.toRight := by ext y; simp
@[simp] lemma toRight_insert_inr : (insert (inr b) s).toRight = insert b s.toRight := by ext y; simp

lemma toLeft_inter : (s ∩ t).toLeft = s.toLeft ∩ t.toLeft := by ext x; simp
lemma toRight_inter : (s ∩ t).toRight = s.toRight ∩ t.toRight := by ext x; simp

lemma toLeft_union : (s ∪ t).toLeft = s.toLeft ∪ t.toLeft := by ext x; simp
lemma toRight_union : (s ∪ t).toRight = s.toRight ∪ t.toRight := by ext x; simp

lemma toLeft_sdiff : (s \ t).toLeft = s.toLeft \ t.toLeft := by ext x; simp
lemma toRight_sdiff : (s \ t).toRight = s.toRight \ t.toRight := by ext x; simp

end Finset

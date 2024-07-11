/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import Mathlib.Order.Antichain
import Mathlib.Order.UpperLower.Basic
import Mathlib.Order.Interval.Set.Basic
import Mathlib.Order.RelIso.Set
import Mathlib.Data.Set.Notation

#align_import order.minimal from "leanprover-community/mathlib"@"59694bd07f0a39c5beccba34bd9f413a160782bf"

/-!
# Minimal/maximal elements of a set

This file defines minimal and maximal of a set with respect to an arbitrary relation.

## Main declarations

* `maximals r s`: Maximal elements of `s` with respect to `r`.
* `minimals r s`: Minimal elements of `s` with respect to `r`.

## TODO

Do we need a `Finset` version?
-/

open Function Set OrderDual Set.Notation

variable {α : Type*} {r r₁ r₂ : α → α → Prop} {P Q : α → Prop} {a x y : α}

section Preorder

variable [Preorder α]

def Minimal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x ≤ y

def Maximal (P : α → Prop) (x : α) : Prop := P x ∧ ∀ ⦃y⦄, P y → x ≤ y → y ≤ x

lemma Minimal.prop (h : Minimal P x) : P x :=
  h.1

lemma Maximal.prop (h : Maximal P x) : P x :=
  h.1

lemma Minimal.le_of_le (h : Minimal P x) (hy : P y) (hle : y ≤ x) : x ≤ y :=
  h.2 hy hle

lemma Maximal.le_of_le (h : Maximal P x) (hy : P y) (hle : x ≤ y) : y ≤ x :=
  h.2 hy hle

@[simp] theorem minimal_toDual_iff : Minimal (fun x ↦ P (ofDual x)) (toDual x) ↔ Maximal P x :=
  Iff.rfl

@[simp] theorem maximal_toDual_iff : Maximal (fun x ↦ P (ofDual x)) (toDual x) ↔ Minimal P x :=
  Iff.rfl

theorem minimal_iff_forall_lt : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, y < x → ¬ P y := by
  simp [Minimal, lt_iff_le_not_le, not_imp_not, imp.swap]

theorem maximal_iff_forall_lt : Maximal P x ↔ P x ∧ ∀ ⦃y⦄, x < y → ¬ P y :=
  minimal_iff_forall_lt (α := αᵒᵈ)

theorem Minimal.not_prop_of_lt (h : Minimal P x) (hlt : y < x) : ¬ P y :=
  (minimal_iff_forall_lt.1 h).2 hlt

theorem Maximal.not_prop_of_lt (h : Maximal P x) (hlt : x < y) : ¬ P y :=
  (maximal_iff_forall_lt.1 h).2 hlt

theorem Minimal.not_lt (h : Minimal P x) (hy : P y) : ¬ (y < x) :=
  fun hlt ↦ h.not_prop_of_lt hlt hy

theorem Maximal.not_lt (h : Maximal P x) (hy : P y) : ¬ (x < y) :=
  fun hlt ↦ h.not_prop_of_lt hlt hy

@[simp] theorem minimal_false : ¬ Minimal (fun _ ↦ False) x := by
  simp [Minimal]

@[simp] theorem maximal_false : ¬ Maximal (fun _ ↦ False) x := by
  simp [Maximal]

@[simp] theorem minimal_eq_iff : Minimal (· = y) x ↔ x = y := by
  simp (config := {contextual := true}) [Minimal]

@[simp] theorem maximal_eq_iff : Maximal (· = y) x ↔ x = y := by
  simp (config := {contextual := true}) [Maximal]

theorem Minimal.or (h : Minimal (fun x ↦ P x ∨ Q x) x) : Minimal P x ∨ Minimal Q x := by
  obtain ⟨(h | h), hmin⟩ := h
  · exact .inl ⟨h, fun y hy hyx ↦ hmin (Or.inl hy) hyx⟩
  exact .inr ⟨h, fun y hy hyx ↦ hmin (Or.inr hy) hyx⟩

theorem Maximal.or (h : Maximal (fun x ↦ P x ∨ Q x) x) : Maximal P x ∨ Maximal Q x :=
  Minimal.or (α := αᵒᵈ) h

theorem Minimal.and_right (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ (P x ∧ Q x)) x :=
  ⟨⟨h.prop, hQ⟩, fun _ hy ↦ h.le_of_le hy.1⟩

theorem Minimal.and_left (h : Minimal P x) (hQ : Q x) : Minimal (fun x ↦ (Q x ∧ P x)) x :=
  ⟨⟨hQ, h.prop⟩, fun _ hy ↦ h.le_of_le hy.2⟩

theorem Maximal.and_right (h : Maximal P x) (hQ : Q x) : Maximal (fun x ↦ (P x ∧ Q x)) x :=
  ⟨⟨h.prop, hQ⟩, fun _ hy ↦ h.le_of_le hy.1⟩

theorem Maximal.and_left (h : Maximal P x) (hQ : Q x) : Maximal (fun x ↦ (Q x ∧ P x)) x :=
  ⟨⟨hQ, h.prop⟩, fun _ hy ↦ h.le_of_le hy.2⟩

theorem minimal_and_iff_right_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ P x ∧ Q x) x ↔ (Minimal P x) ∧ Q x :=
  ⟨fun h ↦ ⟨⟨h.prop.1, fun _ hy hxy ↦ h.le_of_le ⟨hy, hPQ hy⟩ hxy⟩, hPQ h.prop.1⟩,
    fun h ↦ ⟨⟨h.1.prop, hPQ h.1.prop⟩, fun _ hy ↦ h.1.le_of_le hy.1⟩⟩

theorem minimal_and_iff_left_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Minimal (fun x ↦ Q x ∧ P x) x ↔ Q x ∧ (Minimal P x) := by
  simp_rw [iff_comm, and_comm, minimal_and_iff_right_of_imp hPQ, and_comm]

theorem maximal_and_iff_right_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Maximal (fun x ↦ P x ∧ Q x) x ↔ (Maximal P x) ∧ Q x :=
  minimal_and_iff_right_of_imp (α := αᵒᵈ) hPQ

theorem maximal_and_iff_left_of_imp (hPQ : ∀ ⦃x⦄, P x → Q x) :
    Maximal (fun x ↦ Q x ∧ P x) x ↔ Q x ∧ (Maximal P x) :=
  minimal_and_iff_left_of_imp (α := αᵒᵈ) hPQ

@[simp] theorem minimal_minimal : Minimal (Minimal P) x ↔ Minimal P x :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hy hyx ↦ h.le_of_le hy.prop hyx⟩⟩

@[simp] theorem maximal_maximal : Maximal (Maximal P) x ↔ Maximal P x :=
  minimal_minimal (α := αᵒᵈ)

@[simp] theorem maximal_true_subtype {x : Subtype P} :
    Maximal (fun _ ↦ True) x ↔ Maximal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Maximal, hx]

@[simp] theorem minimal_true_subtype {x : Subtype P} :
    Minimal (fun _ ↦ True) x ↔ Minimal P x := by
  obtain ⟨x, hx⟩ := x
  simp [Minimal, hx]

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem Minimal.eq_of_le (hx : Minimal P x) (hy : P y) (hle : y ≤ x) : x = y :=
  (hx.2 hy hle).antisymm hle

theorem Maximal.eq_of_le (hx : Maximal P x) (hy : P y) (hle : x ≤ y) : x = y :=
  hle.antisymm <| hx.2 hy hle

theorem minimal_iff : Minimal P x ↔ P x ∧ ∀ ⦃y⦄, P y → y ≤ x → x = y :=
  ⟨fun h ↦ ⟨h.1, fun _ ↦ h.eq_of_le⟩, fun h ↦ ⟨h.1, fun _ hy hle ↦ (h.2 hy hle).le⟩⟩

theorem maximal_iff : Maximal P x ↔ P x ∧ ∀ ⦃y⦄, P y → x ≤ y → x = y :=
  minimal_iff (α := αᵒᵈ)

theorem minimal_mem_iff {s : Set α} : Minimal (· ∈ s) x ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → y ≤ x → x = y :=
  minimal_iff

theorem maximal_mem_iff {s : Set α} : Maximal (· ∈ s) x ↔ x ∈ s ∧ ∀ ⦃y⦄, y ∈ s → x ≤ y → x = y :=
  maximal_iff

theorem minimal_iff_minimal_of_imp_of_forall (hPQ : ∀ ⦃x⦄, Q x → P x)
    (h : ∀ ⦃x⦄, P x → ∃ y, y ≤ x ∧ Q y) : Minimal P x ↔ Minimal Q x := by
  refine ⟨fun h' ↦ ⟨?_, fun y hy hyx ↦ h'.le_of_le (hPQ hy) hyx⟩,
    fun h' ↦ ⟨hPQ h'.prop, fun y hy hyx ↦ ?_⟩⟩
  · obtain ⟨y, hyx, hy⟩ := h h'.prop
    rwa [((h'.le_of_le (hPQ hy)) hyx).antisymm hyx]
  obtain ⟨z, hzy, hz⟩ := h hy
  exact (h'.le_of_le hz (hzy.trans hyx)).trans hzy

theorem maximal_iff_maximal_of_imp_of_forall (hPQ : ∀ ⦃x⦄, Q x → P x)
    (h : ∀ ⦃x⦄, P x → ∃ y, x ≤ y ∧ Q y) : Maximal P x ↔ Maximal Q x :=
  minimal_iff_minimal_of_imp_of_forall (α := αᵒᵈ) hPQ h

@[simp] theorem minimal_true [OrderBot α] : Minimal (fun _ ↦ True) x ↔ x = ⊥ := by
  simp only [minimal_iff, true_implies, true_and]
  exact ⟨fun h ↦ h bot_le, fun h ↦ by simp [h]⟩

@[simp] theorem maximal_true [OrderTop α] : Maximal (fun _ ↦ True) x ↔ x = ⊤ :=
  minimal_true (α := αᵒᵈ)

end PartialOrder

section Subset

variable {P : Set α → Prop} {s t : Set α}

theorem minimal_iff_forall_ssubset : Minimal P s ↔ P s ∧ ∀ ⦃t⦄, t ⊂ s → ¬ P t :=
  minimal_iff_forall_lt

theorem Minimal.not_prop_of_ssubset (h : Minimal P s) (ht : t < s) : ¬ P t :=
  (minimal_iff_forall_lt.1 h).2 ht

theorem Minimal.not_ssubset (h : Minimal P s) (ht : P t) : ¬ t ⊂ s :=
  h.not_lt ht

theorem minimal_iff_forall_diff_singleton (hP : ∀ ⦃s t⦄, P t → t ⊆ s → P s) :
    Minimal P s ↔ P s ∧ ∀ x ∈ s, ¬ P (s \ {x}) :=
  ⟨fun h ↦ ⟨h.prop, fun x hxs hx ↦ by simpa using h.le_of_le hx diff_subset hxs⟩,
    fun h ↦ ⟨h.1, fun t ht hts x hxs ↦ by_contra fun hxt ↦
        h.2 x hxs <| hP ht (subset_diff_singleton hts hxt)⟩⟩

theorem maximal_iff_forall_ssubset : Maximal P s ↔ P s ∧ ∀ ⦃t⦄, s ⊂ t → ¬ P t :=
  maximal_iff_forall_lt

theorem Maximal.not_prop_of_ssubset (h : Maximal P s) (ht : s < t) : ¬ P t :=
  (maximal_iff_forall_lt.1 h).2 ht

theorem Maximal.not_ssubset (h : Maximal P s) (ht : P t) : ¬ s ⊂ t :=
  h.not_lt ht

theorem maximal_iff_forall_insert (hP : ∀ ⦃s t⦄, P t → s ⊆ t → P s) :
    Maximal P s ↔ P s ∧ ∀ x ∉ s, ¬ P (insert x s) := by
  simp only [Maximal, and_congr_right_iff]
  exact fun _ ↦ ⟨fun h x hxs hx ↦ hxs <| h hx (subset_insert _ _) (mem_insert _ _),
    fun h t ht hst x hxt ↦ by_contra fun hxs ↦ h x hxs (hP ht (insert_subset hxt hst))⟩

/- TODO : generalize `minimal_iff_forall_diff_singleton` and `maximal_iff_forall_insert`
to `StronglyAtomic` orders. -/

end Subset

section Set

variable {s t : Set α}

section Preorder

variable [Preorder α]

theorem setOf_minimal_subset (s : Set α) : {x | Minimal (· ∈ s) x} ⊆ s :=
  sep_subset ..

theorem setOf_maximal_subset (s : Set α) : {x | Minimal (· ∈ s) x} ⊆ s :=
  sep_subset ..

theorem Set.Subsingleton.maximal_mem_iff (h : s.Subsingleton) : Maximal (· ∈ s) x ↔ x ∈ s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

theorem Set.Subsingleton.minimal_mem_iff (h : s.Subsingleton) : Minimal (· ∈ s) x ↔ x ∈ s := by
  obtain (rfl | ⟨x, rfl⟩) := h.eq_empty_or_singleton <;> simp

theorem IsLeast.minimal (h : IsLeast s x) : Minimal (· ∈ s) x :=
  ⟨h.1, fun _b hb _ ↦ h.2 hb⟩

theorem IsGreatest.maximal (h : IsGreatest s x) : Maximal (· ∈ s) x :=
  ⟨h.1, fun _b hb _ ↦ h.2 hb⟩

theorem IsAntichain.minimal_mem_iff (hs : IsAntichain (· ≤ ·) s) : Minimal (· ∈ s) x ↔ x ∈ s :=
  ⟨fun h ↦ h.prop, fun h ↦ ⟨h, fun _ hys hyx ↦ (hs.eq hys h hyx).symm.le⟩⟩

theorem IsAntichain.maximal_mem_iff (hs : IsAntichain (· ≤ ·) s) : Maximal (· ∈ s) x ↔ x ∈ s :=
  hs.to_dual.minimal_mem_iff

/-- If `t` is an antichain shadowing and including the set of maximal elements of `s`,
then `t` is the set of maximal elements of `s`. -/
theorem IsAntichain.eq_maximals (ht : IsAntichain (· ≤ ·) t) (h : ∀ x, Maximal (· ∈ s) x → x ∈ t)
    (hs : ∀ a ∈ t, ∃ b, b ≤ a ∧ Maximal (· ∈ s) b) : {x | Maximal (· ∈ s) x} = t := by
  refine Set.ext fun x ↦ ⟨h _, fun hx ↦ ?_⟩
  obtain ⟨y, hyx, hy⟩ := hs x hx
  rwa [← ht.eq (h y hy) hx hyx]

/-- If `t` is an antichain shadowed by and including the set of minimals elements of `s`,
then `t` is the set of minimal elements of `s`. -/
theorem IsAntichain.eq_minimals (ht : IsAntichain (· ≤ ·) t) (h : ∀ x, Minimal (· ∈ s) x → x ∈ t)
    (hs : ∀ a ∈ t, ∃ b, a ≤ b ∧ Minimal (· ∈ s) b) : {x | Minimal (· ∈ s) x} = t :=
  ht.to_dual.eq_maximals h hs

end Preorder

section PartialOrder

variable [PartialOrder α]

theorem setOf_maximal_antichain (P : α → Prop) : IsAntichain (· ≤ ·) {x | Maximal P x} :=
  fun _ hx _ ⟨hy, _⟩ hne hle ↦ hne (hle.antisymm <| hx.2 hy hle)

theorem setOf_minimal_antichain (P : α → Prop) : IsAntichain (· ≤ ·) {x | Minimal P x} :=
  (setOf_maximal_antichain (α := αᵒᵈ) P).swap

theorem IsAntichain.minimal_mem_upperClosure_iff_mem (hs : IsAntichain (· ≤ ·) s) :
    Minimal (· ∈ upperClosure s) x ↔ x ∈ s := by
  simp only [upperClosure, UpperSet.mem_mk, mem_setOf_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨x, h, rfl.le⟩, fun b ⟨a, has, hab⟩ hbx ↦ ?_⟩⟩
  · obtain ⟨a, has, hax⟩ := h.prop
    rwa [h.eq_of_le ⟨a, has, rfl.le⟩ hax]
  rwa [← hs.eq has h (hab.trans hbx)]

theorem IsAntichain.maximal_mem_lowerClosure_iff_mem (hs : IsAntichain (· ≤ ·) s) :
    Maximal (· ∈ lowerClosure s) x ↔ x ∈ s :=
  hs.to_dual.minimal_mem_upperClosure_iff_mem

theorem IsLeast.minimal_iff (h : IsLeast s a) : Minimal (· ∈ s) x ↔ x = a :=
  ⟨fun h' ↦ h'.eq_of_le h.1 (h.2 h'.prop), fun h' ↦ h' ▸ h.minimal⟩

theorem IsGreatest.maximal_iff (h : IsGreatest s a) : Maximal (· ∈ s) x ↔ x = a :=
  ⟨fun h' ↦ h'.eq_of_le h.1 (h.2 h'.prop), fun h' ↦ h' ▸ h.maximal⟩

end PartialOrder

end Set

section Image

variable [Preorder α] {β : Type*} [Preorder β] {f : α → β} {b : β} {s t : Set α}

theorem minimal_mem_image (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y))
    (hx : Minimal (· ∈ s) x) : Minimal (· ∈ f '' s) (f x) := by
  refine ⟨mem_image_of_mem f hx.prop, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  rw [hf hx.prop hy, hf hy hx.prop]
  exact hx.le_of_le hy

theorem maximal_mem_image {f : α → β} (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y))
    (hx : Maximal (· ∈ s) x) : Maximal (· ∈ f '' s) (f x) :=
  minimal_mem_image (α := αᵒᵈ) (β := βᵒᵈ) (s := s) (fun _ _ hx hy ↦ hf hy hx) hx

theorem OrderEmbedding.minimal_mem_image (f : α ↪o β) (hx : Minimal (· ∈ s) x) :
    Minimal (· ∈ f '' s) (f x) :=
  _root_.minimal_mem_image (by simp [f.le_iff_le]) hx

theorem OrderEmbedding.maximal_mem_image (f : α ↪o β) (hx : Maximal (· ∈ s) x) :
    Maximal (· ∈ f '' s) (f x) :=
  _root_.maximal_mem_image (by simp [f.le_iff_le]) hx

theorem minimal_mem_image_iff (ha : a ∈ s) (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a := by
  refine ⟨fun h ↦ ⟨ha, fun y hys ↦ ?_⟩, minimal_mem_image hf⟩
  rw [← hf ha hys, ← hf hys ha]
  exact h.le_of_le (mem_image_of_mem f hys)

theorem OrderEmbedding.minimal_mem_image_iff {f : α ↪o β} (ha : a ∈ s) :
    Minimal (· ∈ f '' s) (f a) ↔ Minimal (· ∈ s) a :=
  _root_.minimal_mem_image_iff ha (by simp [f.le_iff_le])

theorem maximal_mem_image_iff {f : α → β} (ha : a ∈ s)
    (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    Maximal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  minimal_mem_image_iff (α := αᵒᵈ) (β := βᵒᵈ) (s := s) ha fun _ _ hx hy ↦ hf hy hx

theorem OrderEmbedding.maximal_mem_image_iff {f : α ↪o β} (ha : a ∈ s) :
    Maximal (· ∈ f '' s) (f a) ↔ Maximal (· ∈ s) a :=
  _root_.maximal_mem_image_iff ha (by simp [f.le_iff_le])

theorem OrderEmbedding.minimal_apply_inter_range_iff {f : α ↪o β} {t : Set β} :
    Minimal (· ∈ t ∩ range f) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  refine ⟨fun h ↦ ⟨h.prop.1, fun y hy ↦ ?_⟩, fun h ↦ ⟨⟨h.prop, by simp⟩, ?_⟩⟩
  · rw [← f.le_iff_le, ← f.le_iff_le]
    exact h.le_of_le ⟨hy, by simp⟩
  rintro _ ⟨hyt, ⟨y, rfl⟩⟩
  simp_rw [f.le_iff_le]
  exact h.le_of_le hyt

theorem OrderEmbedding.maximal_apply_inter_range_iff {f : α ↪o β} {t : Set β} :
    Maximal (· ∈ t ∩ range f) (f x) ↔ Maximal (fun x ↦ f x ∈ t) x :=
  f.dual.minimal_apply_inter_range_iff

theorem OrderEmbedding.minimal_apply_iff {f : α ↪o β} {t : Set β} (ht : t ⊆ Set.range f) :
    Minimal (· ∈ t) (f x) ↔ Minimal (fun x ↦ f x ∈ t) x := by
  rw [← f.minimal_apply_inter_range_iff, inter_eq_self_of_subset_left ht]

theorem OrderEmbedding.maximal_apply_iff {f : α ↪o β} {t : Set β} (ht : t ⊆ Set.range f) :
    Maximal (· ∈ t) (f x) ↔ Maximal (fun x ↦ f x ∈ t) x :=
  f.dual.minimal_apply_iff ht

theorem image_setOf_minimals {f : α → β} (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} := by
  refine Set.ext fun x ↦ ⟨?_, fun h : Minimal (· ∈ f '' s) x ↦ ?_⟩
  · rintro ⟨x, (hx : Minimal _ x), rfl⟩
    rwa [mem_setOf, minimal_mem_image_iff hx.prop hf]
  obtain ⟨y, hy, rfl⟩ := h.prop
  rw [minimal_mem_image_iff hy hf] at h
  exact mem_image_of_mem f h

@[simp] theorem OrderEmbedding.image_setOf_minimals {f : α ↪o β} :
    f '' {x | Minimal (· ∈ s) x} = {x | Minimal (· ∈ f '' s) x} :=
  _root_.image_setOf_minimals (by simp [f.le_iff_le])

theorem image_setOf_maximals {f : α → β} (hf : ∀ ⦃x y⦄, x ∈ s → y ∈ s → (f x ≤ f y ↔ x ≤ y)) :
    f '' {x | Maximal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  image_setOf_minimals (α := αᵒᵈ) (β := βᵒᵈ) (s := s) fun _ _ hx hy ↦ hf hy hx

@[simp] theorem OrderEmbedding.image_setOf_maximals {f : α ↪o β} :
    f '' {x | Maximal (· ∈ s) x} = {x | Maximal (· ∈ f '' s) x} :=
  _root_.image_setOf_maximals (by simp [f.le_iff_le])

theorem OrderIso.map_mem_minimals (f : s ≃o t) {x : α}
    (hx : Minimal (· ∈ s) x) : Minimal (· ∈ t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, minimal_true_subtype, hx,
    true_imp_iff, image_univ] using OrderEmbedding.minimal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype t)) (s := univ) (x := ⟨x, hx.prop⟩)

theorem OrderIso.map_mem_maximals (f : s ≃o t) {x : α}
    (hx : Maximal (· ∈ s) x) : Maximal (· ∈ t) (f ⟨x, hx.prop⟩) := by
  simpa only [show t = range (Subtype.val ∘ f) by simp, mem_univ, maximal_true_subtype, hx,
    true_imp_iff, image_univ] using OrderEmbedding.maximal_mem_image
    (f.toOrderEmbedding.trans (OrderEmbedding.subtype t)) (s := univ) (x := ⟨x, hx.prop⟩)

/-- If two sets are order isomorphic, their minimals are also order isomorphic. -/
def OrderIso.mapMinimals (f : s ≃o t) : {x | Minimal (· ∈ s) x} ≃o {x | Minimal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_mem_minimals x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_mem_minimals x.2⟩
  left_inv x := Subtype.ext (by apply congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩)
  right_inv x := Subtype.ext (by apply congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩)
  map_rel_iff' {_ _} := f.map_rel_iff

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
def OrderIso.mapMaximals (f : s ≃o t) : {x | Maximal (· ∈ s) x} ≃o {x | Maximal (· ∈ t) x} where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_mem_maximals x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_mem_maximals x.2⟩
  __ := (show OrderDual.ofDual ⁻¹' s ≃o OrderDual.ofDual ⁻¹' t from f.dual).mapMinimals

theorem OrderEmbedding.inter_preimage_minimals_eq_of_subset (f : α ↪o β) {t : Set β}
    (hts : t ⊆ f '' s) :
    x ∈ s ∩ f ⁻¹' {y | Minimal (· ∈ t) y} ↔ Minimal (· ∈ s ∩ f ⁻¹' t) x := by
  simp_rw [mem_inter_iff, preimage_setOf_eq, mem_setOf_eq, mem_preimage]
  rw [f.minimal_apply_iff (hts.trans (image_subset_range _ _)), minimal_and_iff_left_of_imp]
  exact fun x hx ↦ f.injective.mem_set_image.1 <| hts hx








end Image



-- theorem mem_minimals_iff_forall_lt_not_mem'
--     (rlt : α → α → Prop) [IsNonstrictStrictOrder α r rlt] :
--     x ∈ minimals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt y x → y ∉ s := by
--   simp [minimals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]

-- theorem mem_maximals_iff_forall_lt_not_mem'
--     (rlt : α → α → Prop) [IsNonstrictStrictOrder α r rlt] :
--     x ∈ maximals r s ↔ x ∈ s ∧ ∀ ⦃y⦄, rlt x y → y ∉ s := by
--   simp [maximals, right_iff_left_not_left_of r rlt, not_imp_not, imp.swap (a := _ ∈ _)]

-- theorem minimals_eq_minimals_of_subset_of_forall [IsTrans α r] (hts : t ⊆ s)
--     (h : ∀ x ∈ s, ∃ y ∈ t, r y x) : minimals r s = minimals r t := by
--   refine Set.ext fun a ↦ ⟨fun ⟨has, hmin⟩ ↦ ⟨?_,fun b hbt ↦ hmin (hts hbt)⟩,
--     fun ⟨hat, hmin⟩ ↦ ⟨hts hat, fun b hbs hba ↦ ?_⟩⟩
--   · obtain ⟨a', ha', haa'⟩ := h _ has
--     rwa [antisymm (hmin (hts ha') haa') haa']
--   obtain ⟨b', hb't, hb'b⟩ := h b hbs
--   rwa [antisymm (hmin hb't (Trans.trans hb'b hba)) (Trans.trans hb'b hba)]

-- theorem maximals_eq_maximals_of_subset_of_forall [IsTrans α r] (hts : t ⊆ s)
--     (h : ∀ x ∈ s, ∃ y ∈ t, r x y) : maximals r s = maximals r t :=
--   @minimals_eq_minimals_of_subset_of_forall _ _ _ _ (IsAntisymm.swap r) (IsTrans.swap r) hts h

-- variable (r s)


section Set



-- variable {r r₁ r₂ s t a}

-- -- Porting note (#11215): TODO: use `h.induction_on`
-- theorem Set.Subsingleton.maximals_eq (h : s.Subsingleton) : maximals r s = s := by
--   rcases h.eq_empty_or_singleton with (rfl | ⟨x, rfl⟩)
--   exacts [minimals_empty _, maximals_singleton _ _]
-- #align set.subsingleton.maximals_eq Set.Subsingleton.maximals_eq

-- theorem Set.Subsingleton.minimals_eq (h : s.Subsingleton) : minimals r s = s :=
--   h.maximals_eq
-- #align set.subsingleton.minimals_eq Set.Subsingleton.minimals_eq

-- theorem maximals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
--     maximals r₂ s ⊆ maximals r₁ s := fun a ha =>
--   ⟨ha.1, fun b hb hab => by
--     have := eq_of_mem_maximals ha hb (h _ _ hab)
--     subst this
--     exact hab⟩
-- #align maximals_mono maximals_mono

-- theorem minimals_mono [IsAntisymm α r₂] (h : ∀ a b, r₁ a b → r₂ a b) :
--     minimals r₂ s ⊆ minimals r₁ s := fun a ha =>
--   ⟨ha.1, fun b hb hab => by
--     have := eq_of_mem_minimals ha hb (h _ _ hab)
--     subst this
--     exact hab⟩
-- #align minimals_mono minimals_mono

-- theorem maximals_union : maximals r (s ∪ t) ⊆ maximals r s ∪ maximals r t := by
--   intro a ha
--   obtain h | h := ha.1
--   · exact Or.inl ⟨h, fun b hb => ha.2 <| Or.inl hb⟩
--   · exact Or.inr ⟨h, fun b hb => ha.2 <| Or.inr hb⟩
-- #align maximals_union maximals_union

-- theorem minimals_union : minimals r (s ∪ t) ⊆ minimals r s ∪ minimals r t :=
--   maximals_union
-- #align minimals_union minimals_union

-- theorem maximals_inter_subset : maximals r s ∩ t ⊆ maximals r (s ∩ t) := fun _a ha =>
--   ⟨⟨ha.1.1, ha.2⟩, fun _b hb => ha.1.2 hb.1⟩
-- #align maximals_inter_subset maximals_inter_subset

-- theorem minimals_inter_subset : minimals r s ∩ t ⊆ minimals r (s ∩ t) :=
--   maximals_inter_subset
-- #align minimals_inter_subset minimals_inter_subset

-- theorem inter_maximals_subset : s ∩ maximals r t ⊆ maximals r (s ∩ t) := fun _a ha =>
--   ⟨⟨ha.1, ha.2.1⟩, fun _b hb => ha.2.2 hb.2⟩
-- #align inter_maximals_subset inter_maximals_subset

-- theorem inter_minimals_subset : s ∩ minimals r t ⊆ minimals r (s ∩ t) :=
--   inter_maximals_subset
-- #align inter_minimals_subset inter_minimals_subset

-- theorem IsAntichain.maximals_eq (h : IsAntichain r s) : maximals r s = s :=
--   (maximals_subset _ _).antisymm fun a ha =>
--     ⟨ha, fun b hb hab => by
--       obtain rfl := h.eq ha hb hab
--       exact hab⟩
-- #align is_antichain.maximals_eq IsAntichain.maximals_eq

-- theorem IsAntichain.minimals_eq (h : IsAntichain r s) : minimals r s = s :=
--   h.flip.maximals_eq
-- #align is_antichain.minimals_eq IsAntichain.minimals_eq


section Image

variable {f : α → β} {r : α → α → Prop} {s : β → β → Prop}

section
variable {x : Set α} (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) {a : α}

-- theorem map_mem_minimals (ha : a ∈ minimals r x) : f a ∈ minimals s (f '' x) :=
--   ⟨⟨a, ha.1, rfl⟩, by rintro _ ⟨a', h', rfl⟩; rw [← hf ha.1 h', ← hf h' ha.1]; exact ha.2 h'⟩

-- theorem map_mem_maximals (ha : a ∈ maximals r x) : f a ∈ maximals s (f '' x) :=
--   map_mem_minimals (fun _ _ h₁ h₂ ↦ by exact hf h₂ h₁) ha

-- theorem map_mem_minimals_iff (ha : a ∈ x) : f a ∈ minimals s (f '' x) ↔ a ∈ minimals r x :=
--   ⟨fun ⟨_, hmin⟩ ↦ ⟨ha, fun a' h' ↦ by
--     simpa only [hf h' ha, hf ha h'] using hmin ⟨a', h', rfl⟩⟩, map_mem_minimals hf⟩

-- theorem map_mem_maximals_iff (ha : a ∈ x) : f a ∈ maximals s (f '' x) ↔ a ∈ maximals r x :=
--   map_mem_minimals_iff (fun _ _ h₁ h₂ ↦ by exact hf h₂ h₁) ha

-- theorem image_minimals_of_rel_iff_rel : f '' minimals r x = minimals s (f '' x) := by
--   ext b; refine ⟨?_, fun h ↦ ?_⟩
--   · rintro ⟨a, ha, rfl⟩; exact map_mem_minimals hf ha
--   · obtain ⟨a, ha, rfl⟩ := h.1; exact ⟨a, (map_mem_minimals_iff hf ha).mp h, rfl⟩

-- theorem image_maximals_of_rel_iff_rel : f '' maximals r x = maximals s (f '' x) :=
--   image_minimals_of_rel_iff_rel fun _ _ h₁ h₂ ↦ hf h₂ h₁

-- end

-- theorem RelEmbedding.image_minimals_eq (f : r ↪r s) (x : Set α) :
--     f '' minimals r x = minimals s (f '' x) := by
--   rw [image_minimals_of_rel_iff_rel]; simp [f.map_rel_iff]

-- theorem RelEmbedding.image_maximals_eq (f : r ↪r s) (x : Set α) :
--     f '' maximals r x = maximals s (f '' x) :=
--   f.swap.image_minimals_eq x

section

-- variable [LE α] [LE β] {s : Set α} {t : Set β}

-- theorem image_minimals_univ :
--     Subtype.val '' minimals (· ≤ ·) (univ : Set s) = minimals (· ≤ ·) s := by
--   rw [image_minimals_of_rel_iff_rel, image_univ, Subtype.range_val]; intros; rfl

-- theorem image_maximals_univ :
--     Subtype.val '' maximals (· ≤ ·) (univ : Set s) = maximals (· ≤ ·) s :=
--   image_minimals_univ (α := αᵒᵈ)

nonrec theorem OrderIso.map_mem_minimals (f : s ≃o t) {x : α}
    (hx : x ∈ minimals (· ≤ ·) s) : (f ⟨x, hx.1⟩).val ∈ minimals (· ≤ ·) t := by
  rw [← image_minimals_univ] at hx
  obtain ⟨x, h, rfl⟩ := hx
  convert map_mem_minimals (f := Subtype.val ∘ f) (fun _ _ _ _ ↦ f.map_rel_iff.symm) h
  rw [image_comp, image_univ, f.range_eq, image_univ, Subtype.range_val]

theorem OrderIso.map_mem_maximals (f : s ≃o t) {x : α}
    (hx : x ∈ maximals (· ≤ ·) s) : (f ⟨x, hx.1⟩).val ∈ maximals (· ≤ ·) t :=
  (show OrderDual.ofDual ⁻¹' s ≃o OrderDual.ofDual ⁻¹' t from f.dual).map_mem_minimals hx

/-- If two sets are order isomorphic, their minimals are also order isomorphic. -/
def OrderIso.mapMinimals (f : s ≃o t) : minimals (· ≤ ·) s ≃o minimals (· ≤ ·) t where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_mem_minimals x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_mem_minimals x.2⟩
  left_inv x := Subtype.ext (by apply congr_arg Subtype.val <| f.left_inv ⟨x, x.2.1⟩)
  right_inv x := Subtype.ext (by apply congr_arg Subtype.val <| f.right_inv ⟨x, x.2.1⟩)
  map_rel_iff' {_ _} := f.map_rel_iff

/-- If two sets are order isomorphic, their maximals are also order isomorphic. -/
def OrderIso.mapMaximals (f : s ≃o t) : maximals (· ≤ ·) s ≃o maximals (· ≤ ·) t where
  toFun x := ⟨f ⟨x, x.2.1⟩, f.map_mem_maximals x.2⟩
  invFun x := ⟨f.symm ⟨x, x.2.1⟩, f.symm.map_mem_maximals x.2⟩
  __ := (show OrderDual.ofDual ⁻¹' s ≃o OrderDual.ofDual ⁻¹' t from f.dual).mapMinimals
  -- defeq abuse to fill in the proof fields.
  -- If OrderDual ever becomes a structure, just copy the last three lines from OrderIso.mapMinimals

open OrderDual in
/-- If two sets are antitonically order isomorphic, their minimals are too. -/
def OrderIso.minimalsIsoMaximals (f : s ≃o tᵒᵈ) :
    minimals (· ≤ ·) s ≃o (maximals (· ≤ ·) t)ᵒᵈ where
  toFun x := toDual ⟨↑(ofDual (f ⟨x, x.2.1⟩)), (show s ≃o ofDual ⁻¹' t from f).map_mem_minimals x.2⟩
  invFun x := ⟨f.symm (toDual ⟨_, (ofDual x).2.1⟩),
    (show ofDual ⁻¹' t ≃o s from f.symm).map_mem_minimals x.2⟩
  __ := (show s ≃o ofDual⁻¹' t from f).mapMinimals

open OrderDual in
/-- If two sets are antitonically order isomorphic, their minimals are too. -/
def OrderIso.maximalsIsoMinimals (f : s ≃o tᵒᵈ) :
    maximals (· ≤ ·) s ≃o (minimals (· ≤ ·) t)ᵒᵈ where
  toFun x := toDual ⟨↑(ofDual (f ⟨x, x.2.1⟩)), (show s ≃o ofDual ⁻¹' t from f).map_mem_maximals x.2⟩
  invFun x := ⟨f.symm (toDual ⟨_, (ofDual x).2.1⟩),
    (show ofDual ⁻¹' t ≃o s from f.symm).map_mem_maximals x.2⟩
  __ := (show s ≃o ofDual⁻¹' t from f).mapMaximals

end

theorem inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
    {x : Set α} (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) := by
  ext a
  simp only [minimals, mem_inter_iff, mem_image, and_imp, forall_exists_index,
    forall_apply_eq_imp_iff₂, preimage_setOf_eq, mem_setOf_eq, mem_preimage]
  exact ⟨fun ⟨hax,⟨_,hay⟩,h2⟩ ↦ ⟨⟨hax, hay⟩, fun a₁ ha₁ ha₁y ha₁a ↦
          (hf hax ha₁).mpr (h2 _ ha₁ ha₁y ((hf ha₁ hax).mp ha₁a))⟩ ,
        fun ⟨⟨hax,hay⟩,h⟩ ↦ ⟨hax, ⟨⟨_, hax, rfl⟩, hay⟩, fun a' ha' ha'y hsa' ↦
          (hf hax ha').mp (h ha' ha'y ((hf ha' hax).mpr hsa'))⟩⟩

theorem inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset {x : Set α} {y : Set β}
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) :
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [← inter_eq_self_of_subset_right hy, inter_minimals_preimage_inter_eq_of_rel_iff_rel_on hf,
    preimage_inter, ← inter_assoc, inter_eq_self_of_subset_left (subset_preimage_image f x)]

theorem RelEmbedding.inter_preimage_minimals_eq (f : r ↪r s) (x : Set α) (y : Set β) :
    x ∩ f⁻¹' (minimals s ((f '' x) ∩ y)) = minimals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y

theorem RelEmbedding.inter_preimage_minimals_eq_of_subset {y : Set β} {x : Set α}
    (f : r ↪r s) (h : y ⊆ f '' x) :
    x ∩ f ⁻¹' (minimals s y) = minimals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]

theorem RelEmbedding.minimals_preimage_eq (f : r ↪r s) (y : Set β) :
    minimals r (f ⁻¹' y) = f ⁻¹' minimals s (y ∩ range f) := by
  convert (f.inter_preimage_minimals_eq univ y).symm
  · simp [univ_inter]
  · simp [inter_comm]

theorem RelIso.minimals_preimage_eq (f : r ≃r s) (y : Set β) :
    minimals r (f ⁻¹' y) = f ⁻¹' (minimals s y) := by
  convert f.toRelEmbedding.minimals_preimage_eq y; simp

theorem RelIso.maximals_preimage_eq (f : r ≃r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' (maximals s y) :=
  f.swap.minimals_preimage_eq y

theorem inter_maximals_preimage_inter_eq_of_rel_iff_rel_on {x : Set α}
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (y : Set β) :
    x ∩ f ⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_minimals_preimage_inter_eq_of_rel_iff_rel_on
  exact fun _ _ a b ↦ hf b a

theorem inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset {y : Set β} {x : Set α}
    (hf : ∀ ⦃a a'⦄, a ∈ x → a' ∈ x → (r a a' ↔ s (f a) (f a'))) (hy : y ⊆ f '' x) :
    x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  apply inter_preimage_minimals_eq_of_rel_iff_rel_on_of_subset _ hy
  exact fun _ _ a b ↦ hf b a

theorem RelEmbedding.inter_preimage_maximals_eq (f : r ↪r s) (x : Set α) (y : Set β) :
    x ∩ f⁻¹' (maximals s ((f '' x) ∩ y)) = maximals r (x ∩ f ⁻¹' y) :=
  inter_minimals_preimage_inter_eq_of_rel_iff_rel_on (by simp [f.map_rel_iff]) y

theorem RelEmbedding.inter_preimage_maximals_eq_of_subset {y : Set β} {x : Set α}
    (f : r ↪r s) (h : y ⊆ f '' x) : x ∩ f ⁻¹' (maximals s y) = maximals r (x ∩ f ⁻¹' y) := by
  rw [inter_preimage_maximals_eq_of_rel_iff_rel_on_of_subset _ h]; simp [f.map_rel_iff]

theorem RelEmbedding.maximals_preimage_eq (f : r ↪r s) (y : Set β) :
    maximals r (f ⁻¹' y) = f ⁻¹' maximals s (y ∩ range f) := by
  convert (f.inter_preimage_maximals_eq univ y).symm
  · simp [univ_inter]
  · simp [inter_comm]

end Image

section Interval

variable [PartialOrder α] {a b : α}

@[simp] theorem maximals_Iic (a : α) : maximals (· ≤ ·) (Iic a) = {a} :=
  Set.ext fun _ ↦ ⟨fun h ↦ h.1.antisymm (h.2 rfl.le h.1),
    fun h ↦ ⟨h.trans_le rfl.le, fun _ hba _ ↦ le_trans hba h.symm.le⟩⟩

@[simp] theorem minimals_Ici (a : α) : minimals (· ≤ ·) (Ici a) = {a} :=
  maximals_Iic (α := αᵒᵈ) a

theorem maximals_Icc (hab : a ≤ b) : maximals (· ≤ ·) (Icc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Icc (hab : a ≤ b) : minimals (· ≤ ·) (Icc a b) = {a} := by
  simp_rw [Icc, and_comm (a := (a ≤ _))]; exact maximals_Icc (α := αᵒᵈ) hab

theorem maximals_Ioc (hab : a < b) : maximals (· ≤ ·) (Ioc a b) = {b} :=
  Set.ext fun x ↦ ⟨fun h ↦ h.1.2.antisymm (h.2 ⟨hab, rfl.le⟩ h.1.2),
    fun (h : x = b) ↦ ⟨⟨hab.trans_eq h.symm, h.le⟩, fun _ hy _ ↦ hy.2.trans_eq h.symm⟩⟩

theorem minimals_Ico (hab : a < b) : minimals (· ≤ ·) (Ico a b) = {a} := by
  simp_rw [Ico, and_comm (a := _ ≤ _)]; exact maximals_Ioc (α := αᵒᵈ) hab

end Interval

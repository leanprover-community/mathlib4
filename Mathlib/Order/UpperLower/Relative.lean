/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Set.Image
import Mathlib.Data.SetLike.Basic
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.SetNotation

/-!
# Properties of relative upper/lower sets

This file proves results on `IsRelUpperSet` and `IsRelLowerSet`.
-/

open Set

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*} {s t : Set α} {a : α} {P : α → Prop}

section LE

variable [LE α]

lemma IsRelUpperSet.prop_of_mem (hs : IsRelUpperSet s P) (h : a ∈ s) : P a := (hs h).1
lemma IsRelLowerSet.prop_of_mem (hs : IsRelLowerSet s P) (h : a ∈ s) : P a := (hs h).1

@[simp] lemma isRelUpperSet_empty : IsRelUpperSet (∅ : Set α) P := fun _ ↦ False.elim
@[simp] lemma isRelLowerSet_empty : IsRelLowerSet (∅ : Set α) P := fun _ ↦ False.elim

@[simp] lemma isRelUpperSet_self : IsRelUpperSet s s := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩
@[simp] lemma isRelLowerSet_self : IsRelLowerSet s s := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩

lemma IsRelUpperSet.union (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) :
    IsRelUpperSet (s ∪ t) P := fun b mb ↦ by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y ↦ .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y ↦ .inr ((ht h).2 x y)⟩

lemma IsRelLowerSet.union (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) :
    IsRelLowerSet (s ∪ t) P := fun b mb ↦ by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y ↦ .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y ↦ .inr ((ht h).2 x y)⟩

lemma IsRelUpperSet.inter (hs : IsRelUpperSet s P) (ht : IsRelUpperSet t P) :
    IsRelUpperSet (s ∩ t) P := fun b ⟨bs, bt⟩ ↦ by
  simp_all only [IsRelUpperSet, true_and]
  exact fun _ x y ↦ ⟨(hs bs).2 x y, (ht bt).2 x y⟩

lemma IsRelLowerSet.inter (hs : IsRelLowerSet s P) (ht : IsRelLowerSet t P) :
    IsRelLowerSet (s ∩ t) P := fun b ⟨bs, bt⟩ ↦ by
  simp_all only [IsRelLowerSet, true_and]
  exact fun _ x y ↦ ⟨(hs bs).2 x y, (ht bt).2 x y⟩

lemma isRelUpperSet_sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelUpperSet s P) :
    IsRelUpperSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩

lemma isRelLowerSet_sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelLowerSet s P) :
    IsRelLowerSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩

lemma isRelUpperSet_iUnion {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) P) :
    IsRelUpperSet (⋃ i, f i) P :=
  isRelUpperSet_sUnion <| forall_mem_range.2 hf

lemma isRelLowerSet_iUnion {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) P) :
    IsRelLowerSet (⋃ i, f i) P :=
  isRelLowerSet_sUnion <| forall_mem_range.2 hf

lemma isRelUpperSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋃ (i) (j), f i j) P :=
  isRelUpperSet_iUnion fun i ↦ isRelUpperSet_iUnion <| hf i

lemma isRelLowerSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋃ (i) (j), f i j) P :=
  isRelLowerSet_iUnion fun i ↦ isRelLowerSet_iUnion <| hf i

lemma isRelUpperSet_sInter {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelUpperSet s P) :
    IsRelUpperSet (⋂₀ S) P := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩

lemma isRelLowerSet_sInter {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelLowerSet s P) :
    IsRelLowerSet (⋂₀ S) P := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩

lemma isRelUpperSet_iInter [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) P) :
    IsRelUpperSet (⋂ i, f i) P :=
  isRelUpperSet_sInter (range_nonempty f) <| forall_mem_range.2 hf

lemma isRelLowerSet_iInter [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) P) :
    IsRelLowerSet (⋂ i, f i) P :=
  isRelLowerSet_sInter (range_nonempty f) <| forall_mem_range.2 hf

lemma isRelUpperSet_iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋂ (i) (j), f i j) P :=
  isRelUpperSet_iInter fun i => isRelUpperSet_iInter <| hf i

lemma isRelLowerSet_iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋂ (i) (j), f i j) P :=
  isRelLowerSet_iInter fun i => isRelLowerSet_iInter <| hf i

lemma isRelUpperSet_iff_isUpperSet_subtype {s : Set { x // P x }} :
    IsRelUpperSet (Subtype.val '' s) P ↔ IsUpperSet s := by
  refine ⟨fun h a b x y ↦ ?_, fun h a x ↦ ?_⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, SetCoe.ext_iff, exists_eq_right] using (h ma).2 x b.2
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show a ≤ ⟨b, y⟩ by exact x) ma]⟩

lemma isRelLowerSet_iff_isLowerSet_subtype {s : Set { x // P x }} :
    IsRelLowerSet (Subtype.val '' s) P ↔ IsLowerSet s := by
  refine ⟨fun h a b x y ↦ ?_, fun h a x ↦ ?_⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, SetCoe.ext_iff, exists_eq_right] using (h ma).2 x b.2
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show ⟨b, y⟩ ≤ a by exact x) ma]⟩

instance : SetLike (RelUpperSet P) α where
  coe := RelUpperSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

instance : SetLike (RelLowerSet P) α where
  coe := RelLowerSet.carrier
  coe_injective' s t h := by cases s; cases t; congr

lemma RelUpperSet.isRelUpperSet (u : RelUpperSet P) : IsRelUpperSet u P := u.isRelUpperSet'
lemma RelLowerSet.isRelLowerSet (l : RelLowerSet P) : IsRelLowerSet l P := l.isRelLowerSet'

end LE

section Preorder

variable [Preorder α] {c : α}

lemma isRelUpperSet_Icc_Iic : IsRelUpperSet (Icc a c) (Iic c) := fun _ b ↦ by
  change _ ≤ c ∧ ∀ ⦃b : α⦄, _ → b ≤ c → _
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ ↦ b.1.trans x

lemma isRelLowerSet_Icc_Ici : IsRelLowerSet (Icc c a) (Ici c) := fun _ b ↦ by
  change c ≤ _ ∧ ∀ ⦃b : α⦄, _ → c ≤ b → _
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ ↦ x.trans b.2

end Preorder

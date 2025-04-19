/-
Copyright (c) 2025 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
import Mathlib.Data.Set.Image
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.SetNotation

/-!
# Properties of relative upper/lower sets

This file proves results on `IsRelUpperSet` and `IsRelLowerSet`.
-/

open Set

variable {α : Type*} {ι : Sort*} {κ : ι → Sort*} {s t : Set α} {a c : α}

section LE

variable [LE α]

lemma IsRelUpperSet.le_of_mem (hs : IsRelUpperSet s c) (h : a ∈ s) : a ≤ c := (hs h).1

lemma IsRelLowerSet.ge_of_mem (hs : IsRelLowerSet s c) (h : a ∈ s) : c ≤ a := (hs h).1

@[simp]
lemma isRelUpperSet_empty : IsRelUpperSet (∅ : Set α) c := fun _ ↦ False.elim

@[simp]
lemma isRelLowerSet_empty : IsRelLowerSet (∅ : Set α) c := fun _ ↦ False.elim

lemma IsRelUpperSet.union (hs : IsRelUpperSet s c) (ht : IsRelUpperSet t c) :
    IsRelUpperSet (s ∪ t) c := fun b mb ↦ by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y ↦ .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y ↦ .inr ((ht h).2 x y)⟩

lemma IsRelLowerSet.union (hs : IsRelLowerSet s c) (ht : IsRelLowerSet t c) :
    IsRelLowerSet (s ∪ t) c := fun b mb ↦ by
  cases mb with
  | inl h => exact ⟨(hs h).1, fun _ x y ↦ .inl ((hs h).2 x y)⟩
  | inr h => exact ⟨(ht h).1, fun _ x y ↦ .inr ((ht h).2 x y)⟩

lemma IsRelUpperSet.inter (hs : IsRelUpperSet s c) (ht : IsRelUpperSet t c) :
    IsRelUpperSet (s ∩ t) c := fun b ⟨bs, bt⟩ ↦ by
  simp_all only [IsRelUpperSet, true_and]
  exact fun _ x y ↦ ⟨(hs bs).2 x y, (ht bt).2 x y⟩

lemma IsRelLowerSet.inter (hs : IsRelLowerSet s c) (ht : IsRelLowerSet t c) :
    IsRelLowerSet (s ∩ t) c := fun b ⟨bs, bt⟩ ↦ by
  simp_all only [IsRelLowerSet, true_and]
  exact fun _ x y ↦ ⟨(hs bs).2 x y, (ht bt).2 x y⟩

lemma isRelUpperSet_sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelUpperSet s c) :
    IsRelUpperSet (⋃₀ S) c := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩

lemma isRelLowerSet_sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelLowerSet s c) :
    IsRelLowerSet (⋃₀ S) c := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩

lemma isRelUpperSet_iUnion {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) c) :
    IsRelUpperSet (⋃ i, f i) c :=
  isRelUpperSet_sUnion <| forall_mem_range.2 hf

lemma isRelLowerSet_iUnion {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) c) :
    IsRelLowerSet (⋃ i, f i) c :=
  isRelLowerSet_sUnion <| forall_mem_range.2 hf

lemma isRelUpperSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) c) :
    IsRelUpperSet (⋃ (i) (j), f i j) c :=
  isRelUpperSet_iUnion fun i ↦ isRelUpperSet_iUnion <| hf i

lemma isRelLowerSet_iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) c) :
    IsRelLowerSet (⋃ (i) (j), f i j) c :=
  isRelLowerSet_iUnion fun i ↦ isRelLowerSet_iUnion <| hf i

lemma isRelUpperSet_sInter {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelUpperSet s c) :
    IsRelUpperSet (⋂₀ S) c := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩

lemma isRelLowerSet_sInter {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelLowerSet s c) :
    IsRelLowerSet (⋂₀ S) c := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩

lemma isRelUpperSet_iInter [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) c) :
    IsRelUpperSet (⋂ i, f i) c :=
  isRelUpperSet_sInter (range_nonempty f) <| forall_mem_range.2 hf

lemma isRelLowerSet_iInter [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) c) :
    IsRelLowerSet (⋂ i, f i) c :=
  isRelLowerSet_sInter (range_nonempty f) <| forall_mem_range.2 hf

lemma isRelUpperSet_iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) c) :
    IsRelUpperSet (⋂ (i) (j), f i j) c :=
  isRelUpperSet_iInter fun i => isRelUpperSet_iInter <| hf i

lemma isRelLowerSet_iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) c) :
    IsRelLowerSet (⋂ (i) (j), f i j) c :=
  isRelLowerSet_iInter fun i => isRelLowerSet_iInter <| hf i

lemma isRelUpperSet_iff_isUpperSet_subtype {s : Set { x // x ≤ c }} :
    IsRelUpperSet (Subtype.val '' s) c ↔ IsUpperSet s := by
  refine ⟨fun h a b x y ↦ ?_, fun h a x ↦ ?_⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, SetCoe.ext_iff, exists_eq_right] using (h ma).2 x b.2
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show a ≤ ⟨b, y⟩ by exact x) ma]⟩

lemma isRelLowerSet_iff_isLowerSet_subtype {s : Set { x // c ≤ x }} :
    IsRelLowerSet (Subtype.val '' s) c ↔ IsLowerSet s := by
  refine ⟨fun h a b x y ↦ ?_, fun h a x ↦ ?_⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, SetCoe.ext_iff, exists_eq_right] using (h ma).2 x b.2
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show ⟨b, y⟩ ≤ a by exact x) ma]⟩

end LE

section Preorder

variable [Preorder α]

lemma isRelUpperSet_Iic : IsRelUpperSet (Iic c) c := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩

lemma isRelLowerSet_Ici : IsRelLowerSet (Ici c) c := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩

lemma isRelUpperSet_Icc : IsRelUpperSet (Icc a c) c := fun _ b ↦ by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ ↦ b.1.trans x

lemma isRelLowerSet_Icc : IsRelLowerSet (Icc c a) c := fun _ b ↦ by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ ↦ x.trans b.2

end Preorder

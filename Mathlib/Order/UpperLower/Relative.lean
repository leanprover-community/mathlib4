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

@[simp] lemma isRelUpperSet_self : IsRelUpperSet s (· ∈ s) := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩
@[simp] lemma isRelLowerSet_self : IsRelLowerSet s (· ∈ s) := fun _ b ↦ ⟨b, fun _ _ ↦ id⟩

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

protected lemma IsRelUpperSet.sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelUpperSet s P) :
    IsRelUpperSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩

protected lemma IsRelLowerSet.sUnion {S : Set (Set α)} (hS : ∀ s ∈ S, IsRelLowerSet s P) :
    IsRelLowerSet (⋃₀ S) P := fun _ ⟨s, ms, mb⟩ ↦
  ⟨(hS s ms mb).1, fun _ x y ↦ ⟨s, ms, (hS s ms mb).2 x y⟩⟩

protected lemma IsRelUpperSet.iUnion {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) P) :
    IsRelUpperSet (⋃ i, f i) P :=
  .sUnion (forall_mem_range.2 hf)

protected lemma IsRelLowerSet.iUnion {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) P) :
    IsRelLowerSet (⋃ i, f i) P :=
  .sUnion (forall_mem_range.2 hf)

protected lemma IsRelUpperSet.iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋃ (i) (j), f i j) P :=
  .iUnion fun i ↦ .iUnion (hf i)

protected lemma IsRelLowerSet.iUnion₂ {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋃ (i) (j), f i j) P :=
  .iUnion fun i ↦ .iUnion (hf i)

protected lemma IsRelUpperSet.sInter
    {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelUpperSet s P) :
    IsRelUpperSet (⋂₀ S) P := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩

protected lemma IsRelLowerSet.sInter
    {S : Set (Set α)} (hS : S.Nonempty) (hf : ∀ s ∈ S, IsRelLowerSet s P) :
    IsRelLowerSet (⋂₀ S) P := fun b mb ↦ by
  obtain ⟨s₀, ms₀⟩ := hS
  refine ⟨(hf s₀ ms₀ (mb s₀ ms₀)).1, fun _ x y s ms ↦ (hf s ms (mb s ms)).2 x y⟩

protected lemma IsRelUpperSet.iInter
    [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelUpperSet (f i) P) : IsRelUpperSet (⋂ i, f i) P :=
  .sInter (range_nonempty f) (forall_mem_range.2 hf)

protected lemma IsRelLowerSet.iInter
    [Nonempty ι] {f : ι → Set α} (hf : ∀ i, IsRelLowerSet (f i) P) : IsRelLowerSet (⋂ i, f i) P :=
  .sInter (range_nonempty f) (forall_mem_range.2 hf)

protected lemma IsRelUpperSet.iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelUpperSet (f i j) P) :
    IsRelUpperSet (⋂ (i) (j), f i j) P :=
  .iInter fun i ↦ .iInter (hf i)

protected lemma IsRelLowerSet.iInter₂ [Nonempty ι] [∀ i, Nonempty (κ i)]
    {f : ∀ i, κ i → Set α} (hf : ∀ i j, IsRelLowerSet (f i j) P) :
    IsRelLowerSet (⋂ (i) (j), f i j) P :=
  .iInter fun i ↦ .iInter (hf i)

lemma isUpperSet_subtype_iff_isRelUpperSet {s : Set { x // P x }} :
    IsUpperSet s ↔ IsRelUpperSet (Subtype.val '' s) P := by
  refine ⟨fun h a x ↦ ?_, fun h a b x y ↦ ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show a ≤ ⟨b, y⟩ by exact x) ma]⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, SetCoe.ext_iff, exists_eq_right] using (h ma).2 x b.2

lemma isLowerSet_subtype_iff_isRelLowerSet {s : Set { x // P x }} :
    IsLowerSet s ↔ IsRelLowerSet (Subtype.val '' s) P := by
  refine ⟨fun h a x ↦ ?_, fun h a b x y ↦ ?_⟩
  · obtain ⟨a, ma, rfl⟩ := x
    exact ⟨a.2, fun b x y ↦ by simpa [h (show ⟨b, y⟩ ≤ a by exact x) ma]⟩
  · have ma : a.1 ∈ Subtype.val '' s := by simp [a.2, y]
    simpa only [mem_image, SetCoe.ext_iff, exists_eq_right] using (h ma).2 x b.2

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

lemma isRelUpperSet_Icc_le : IsRelUpperSet (Icc a c) (· ≤ c) := fun _ b ↦ by
  simp_all only [mem_Icc, and_true, true_and]
  exact fun _ x _ ↦ b.1.trans x

lemma isRelLowerSet_Icc_ge : IsRelLowerSet (Icc c a) (c ≤ ·) := fun _ b ↦ by
  simp_all only [mem_Icc, true_and]
  exact fun _ x _ ↦ x.trans b.2

end Preorder

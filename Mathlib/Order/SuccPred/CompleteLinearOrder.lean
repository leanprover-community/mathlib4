/-
Copyright (c) 2023 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import Mathlib.Order.SuccPred.Limit
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!

# Relation between `IsSuccLimit` and `iSup` in (conditionally) complete linear orders.

-/

open Order

variable {ι α : Type*}

/-! ### ConditionallyCompleteLinearOrder -/

lemma csSup_mem_of_not_isSuccLimit [ConditionallyCompleteLinearOrder α]
    {s : Set α} (hne : s.Nonempty) (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) :
    sSup s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := exists_lt_of_lt_csSup hne hy.lt
  exact eq_of_le_of_not_lt (le_csSup hbdd his) (hy.2 hi) ▸ his

lemma exists_of_not_isSuccLimit_ciSup [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (hx : ¬ IsSuccLimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  csSup_mem_of_not_isSuccLimit (Set.range_nonempty f) hf hx

lemma exists_of_ciSup_eq_of_not_isSuccLimit [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (x : α) (hx : ¬ IsSuccLimit x) (h : ⨆ i, f i = x) :
    ∃ i, f i = x :=
  h ▸ exists_of_not_isSuccLimit_ciSup f hf (h ▸ hx)

lemma csInf_mem_of_not_isSuccLimit [ConditionallyCompleteLinearOrder α]
    {s : Set α} (hne : s.Nonempty) (hbdd : BddBelow s) (hlim : ¬ IsPredLimit (sInf s)) :
    sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := exists_lt_of_csInf_lt hne hy.lt
  exact eq_of_le_of_not_lt (csInf_le hbdd his) (hy.2 · hi) ▸ his

lemma exists_of_ciInf_eq_of_not_isPredLimit [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddBelow (Set.range f)) (x : α) (hx : ¬ IsPredLimit x) (h : ⨅ i, f i = x) :
    ∃ i, f i = x :=
  exists_of_ciSup_eq_of_not_isSuccLimit (OrderDual.toDual ∘ f) hf (OrderDual.toDual x) (by simpa) h

lemma exists_eq_ciInf_of_not_isPredLimit [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddBelow (Set.range f)) (hx : ¬ IsPredLimit (⨅ i, f i)) :
    ∃ i, f i = ⨅ i, f i :=
  exists_of_ciInf_eq_of_not_isPredLimit f hf _ hx rfl

/-!
### ConditionallyCompleteLinearOrder

The lemma names are primed to distinguish from the version in `ConditionallyCompleteLinearOrder`.
-/

lemma csSup_mem_of_not_isSuccLimit' [ConditionallyCompleteLinearOrderBot α]
    {s : Set α} (hbdd : BddAbove s) (hlim : ¬ IsSuccLimit (sSup s)) :
    sSup s ∈ s := by
  obtain (rfl|hs) := s.eq_empty_or_nonempty
  · simp [isSuccLimit_bot] at hlim
  · exact csSup_mem_of_not_isSuccLimit hs hbdd hlim

lemma exists_of_ciSup_eq_of_not_isSuccLimit' {ι α} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (x : α) (hx : ¬ IsSuccLimit x) (h : ⨆ i, f i = x) :
    ∃ i, f i = x := by
  subst h
  exact csSup_mem_of_not_isSuccLimit' hf hx

lemma exists_eq_ciSup_of_not_isSuccLimit' {ι α} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (hx : ¬ IsSuccLimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  exists_of_ciSup_eq_of_not_isSuccLimit' f hf _ hx rfl

/-! ### CompleteLinearOrder -/

lemma sSup_mem_of_not_isSuccLimit [CompleteLinearOrder α]
    {s : Set α} (hlim : ¬ IsSuccLimit (sSup s)) :
    sSup s ∈ s :=
  csSup_mem_of_not_isSuccLimit' (OrderTop.bddAbove _) hlim

lemma exists_of_iSup_eq_of_not_isSuccLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (x : α) (hx : ¬ IsSuccLimit x) (h : ⨆ i, f i = x) : ∃ i, f i = x :=
  exists_of_ciSup_eq_of_not_isSuccLimit' f (OrderTop.bddAbove _) x hx h

lemma exists_eq_iSup_of_not_isSuccLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (hf : ¬ IsSuccLimit (⨆ i, f i)) : ∃ i, f i = ⨆ i, f i :=
  exists_of_iSup_eq_of_not_isSuccLimit f _ hf rfl

lemma sInf_mem_of_not_isSuccLimit [CompleteLinearOrder α]
    {s : Set α} (hlim : ¬ IsPredLimit (sInf s)) :
    sInf s ∈ s := by
  obtain ⟨y, hy⟩ := not_forall_not.mp hlim
  obtain ⟨i, his, hi⟩ := sInf_lt_iff.mp hy.lt
  exact eq_of_le_of_not_lt (sInf_le his) (hy.2 · hi) ▸ his

lemma exists_of_iInf_eq_of_not_isPredLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (x : α) (hx : ¬ IsPredLimit x) (h : ⨅ i, f i = x) :∃ i, f i = x :=
  exists_of_iSup_eq_of_not_isSuccLimit (OrderDual.toDual ∘ f) (OrderDual.toDual x) (by simpa) h

lemma exists_eq_iInf_of_not_isPredLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (hx : ¬ IsPredLimit (⨅ i, f i)) : ∃ i, f i = ⨅ i, f i :=
  exists_of_iInf_eq_of_not_isPredLimit f _ hx rfl

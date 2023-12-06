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

variable {ι α : Type*}

lemma exists_of_ciSup_eq_of_not_isSuccLimit [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (x : α)
    (hx : ¬ Order.IsSuccLimit x)
    (h : ⨆ i, f i = x) : ∃ i, f i = x := by
  by_contra h'
  obtain ⟨y, hy⟩ := not_forall_not.mp hx
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup (hy.lt.trans_eq h.symm)
  exact hy.2 hi (lt_of_le_of_ne ((le_ciSup hf i).trans_eq h) (not_exists.mp h' i))

lemma exists_of_not_isSuccLimit_ciSup [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddAbove (Set.range f))
    (hx : ¬ Order.IsSuccLimit (⨆ i, f i)) : ∃ i, f i = ⨆ i, f i :=
  exists_of_ciSup_eq_of_not_isSuccLimit f hf _ hx rfl

lemma exists_of_ciSup_eq_of_not_isSuccLimit' {ι α} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (x : α) (hx : ¬ Order.IsSuccLimit x)
    (h : ⨆ i, f i = x) : ∃ i, f i = x := by
  by_contra h'
  obtain ⟨y, hy⟩ := not_forall_not.mp hx
  obtain ⟨i, hi⟩ := exists_lt_of_lt_ciSup' (hy.lt.trans_eq h.symm)
  exact hy.2 hi (lt_of_le_of_ne ((le_ciSup hf i).trans_eq h) (not_exists.mp h' i))

lemma exists_eq_ciSup_of_not_isSuccLimit' {ι α} [ConditionallyCompleteLinearOrderBot α]
    (f : ι → α) (hf : BddAbove (Set.range f)) (hx : ¬ Order.IsSuccLimit (⨆ i, f i)) :
    ∃ i, f i = ⨆ i, f i :=
  exists_of_ciSup_eq_of_not_isSuccLimit' f hf _ hx rfl

lemma exists_of_iSup_eq_of_not_isSuccLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (x : α) (hx : ¬ Order.IsSuccLimit x) (h : ⨆ i, f i = x) : ∃ i, f i = x :=
  exists_of_ciSup_eq_of_not_isSuccLimit' f (OrderTop.bddAbove _) x hx h

lemma exists_eq_iSup_of_not_isSuccLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (hf : ¬ Order.IsSuccLimit (⨆ i, f i)) : ∃ i, f i = ⨆ i, f i :=
  exists_of_iSup_eq_of_not_isSuccLimit f _ hf rfl

lemma exists_of_ciInf_eq_of_not_isPredLimit [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddBelow (Set.range f)) (x : α) (hx : ¬ Order.IsPredLimit x)
    (h : ⨅ i, f i = x) : ∃ i, f i = x :=
  exists_of_ciSup_eq_of_not_isSuccLimit (OrderDual.toDual ∘ f) hf (OrderDual.toDual x) (by simpa) h

lemma exists_eq_ciInf_of_not_isPredLimit [Nonempty ι] [ConditionallyCompleteLinearOrder α]
    (f : ι → α) (hf : BddBelow (Set.range f)) (hx : ¬ Order.IsPredLimit (⨅ i, f i)) :
    ∃ i, f i = ⨅ i, f i :=
  exists_of_ciInf_eq_of_not_isPredLimit f hf _ hx rfl

lemma exists_of_iInf_eq_of_not_isPredLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (x : α)
    (hx : ¬ Order.IsPredLimit x)
    (h : ⨅ i, f i = x) : ∃ i, f i = x :=
  exists_of_iSup_eq_of_not_isSuccLimit (OrderDual.toDual ∘ f) (OrderDual.toDual x) (by simpa) h

lemma exists_eq_iInf_of_not_isPredLimit {ι α} [CompleteLinearOrder α]
    (f : ι → α) (hx : ¬ Order.IsPredLimit (⨅ i, f i)) : ∃ i, f i = ⨅ i, f i :=
  exists_of_iInf_eq_of_not_isPredLimit f _ hx rfl

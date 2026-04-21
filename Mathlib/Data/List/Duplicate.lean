/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
module

public import Mathlib.Data.List.Nodup

/-!
# List duplicates

## Main definitions

* `List.Duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `List.Duplicate x l`.

-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section


variable {α : Type*}

namespace List

/-- Property that an element `x : α` of `l : List α` can be found in the list more than once. -/
inductive Duplicate (x : α) : List α → Prop
  | cons_mem {l : List α} : x ∈ l → Duplicate x (x :: l)
  | cons_duplicate {y : α} {l : List α} : Duplicate x l → Duplicate x (y :: l)

local infixl:50 " ∈+ " => List.Duplicate

variable {l : List α} {x : α}

theorem Mem.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l :=
  Duplicate.cons_mem h

theorem Duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l :=
  Duplicate.cons_duplicate h

theorem Duplicate.mem (h : x ∈+ l) : x ∈ l := by
  induction h with
  | cons_mem => exact mem_cons_self
  | cons_duplicate _ hm => exact mem_cons_of_mem _ hm

theorem Duplicate.mem_cons_self (h : x ∈+ x :: l) : x ∈ l := by
  obtain h | h := h
  · exact h
  · exact h.mem

@[simp]
theorem duplicate_cons_self_iff : x ∈+ x :: l ↔ x ∈ l :=
  ⟨Duplicate.mem_cons_self, Mem.duplicate_cons_self⟩

theorem Duplicate.ne_nil (h : x ∈+ l) : l ≠ [] := fun H => (mem_nil_iff x).mp (H ▸ h.mem)

@[simp]
theorem not_duplicate_nil (x : α) : ¬x ∈+ [] := fun H => H.ne_nil rfl

theorem Duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] := by
  induction h with
  | cons_mem h => simp [ne_nil_of_mem h]
  | cons_duplicate h => simp [ne_nil_of_mem h.mem]

@[simp]
theorem not_duplicate_singleton (x y : α) : ¬x ∈+ [y] := fun H => H.ne_singleton _ rfl

theorem Duplicate.elim_nil (h : x ∈+ []) : False :=
  not_duplicate_nil x h

theorem Duplicate.elim_singleton {y : α} (h : x ∈+ [y]) : False :=
  not_duplicate_singleton x y h

theorem duplicate_cons_iff {y : α} : x ∈+ y :: l ↔ y = x ∧ x ∈ l ∨ x ∈+ l := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain hm | hm := h
    · exact Or.inl ⟨rfl, hm⟩
    · exact Or.inr hm
  · rcases h with (⟨rfl | h⟩ | h)
    · simpa
    · exact h.cons_duplicate

theorem Duplicate.of_duplicate_cons {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l := by
  simpa [duplicate_cons_iff, hx.symm] using h

theorem duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : x ∈+ y :: l ↔ x ∈+ l := by
  simp [duplicate_cons_iff, hne.symm]

theorem Duplicate.mono_sublist {l' : List α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' := by
  induction h with
  | slnil => exact hx
  | cons y _ IH => exact (IH hx).duplicate_cons _
  | cons_cons y h IH =>
    rw [duplicate_cons_iff] at hx ⊢
    rcases hx with (⟨rfl, hx⟩ | hx)
    · simp [h.subset hx]
    · simp [IH hx]

/-- The contrapositive of `List.nodup_iff_sublist`. -/
theorem duplicate_iff_sublist : x ∈+ l ↔ [x, x] <+ l := by
  induction l with
  | nil => simp
  | cons y l IH =>
    by_cases hx : x = y
    · simp [hx, cons_sublist_cons, singleton_sublist]
    · rw [duplicate_cons_iff_of_ne hx, IH]
      refine ⟨sublist_cons_of_sublist y, fun h => ?_⟩
      cases h
      · assumption
      · contradiction

theorem nodup_iff_forall_not_duplicate : Nodup l ↔ ∀ x : α, ¬x ∈+ l := by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]

theorem exists_duplicate_iff_not_nodup : (∃ x : α, x ∈+ l) ↔ ¬Nodup l := by
  simp [nodup_iff_forall_not_duplicate]

theorem Duplicate.not_nodup (h : x ∈+ l) : ¬Nodup l := fun H =>
  nodup_iff_forall_not_duplicate.mp H _ h

theorem duplicate_iff_two_le_count [DecidableEq α] : x ∈+ l ↔ 2 ≤ count x l := by
  simp [replicate_succ, duplicate_iff_sublist, ← replicate_sublist_iff]

instance decidableDuplicate [DecidableEq α] (x : α) : ∀ l : List α, Decidable (x ∈+ l)
  | [] => isFalse (not_duplicate_nil x)
  | y :: l =>
    match decidableDuplicate x l with
    | isTrue h => isTrue (h.duplicate_cons y)
    | isFalse h =>
      if hx : y = x ∧ x ∈ l then isTrue (hx.left.symm ▸ List.Mem.duplicate_cons_self hx.right)
      else isFalse (by simpa [duplicate_cons_iff, h] using hx)

end List

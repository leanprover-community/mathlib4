/-
Copyright (c) 2021 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky, Chris Hughes
-/
import Mathlib.Data.List.Nodup

#align_import data.list.duplicate from "leanprover-community/mathlib"@"f694c7dead66f5d4c80f446c796a5aad14707f0e"

/-!
# List duplicates

## Main definitions

* `List.Duplicate x l : Prop` is an inductive property that holds when `x` is a duplicate in `l`

## Implementation details

In this file, `x ∈+ l` notation is shorthand for `List.Duplicate x l`.

-/


variable {α : Type*}

namespace List

/-- Property that an element `x : α` of `l : List α` can be found in the list more than once. -/
inductive Duplicate (x : α) : List α → Prop
  | cons_mem {l : List α} : x ∈ l → Duplicate x (x :: l)
  | cons_duplicate {y : α} {l : List α} : Duplicate x l → Duplicate x (y :: l)
#align list.duplicate List.Duplicate

-- mathport name: «expr ∈+ »
local infixl:50 " ∈+ " => List.Duplicate

variable {l : List α} {x : α}

theorem Mem.duplicate_cons_self (h : x ∈ l) : x ∈+ x :: l :=
  Duplicate.cons_mem h
#align list.mem.duplicate_cons_self List.Mem.duplicate_cons_self

theorem Duplicate.duplicate_cons (h : x ∈+ l) (y : α) : x ∈+ y :: l :=
  Duplicate.cons_duplicate h
#align list.duplicate.duplicate_cons List.Duplicate.duplicate_cons

theorem Duplicate.mem (h : x ∈+ l) : x ∈ l := by
  induction' h with l' _ y l' _ hm
  -- ⊢ x ∈ x :: l'
  · exact mem_cons_self _ _
    -- 🎉 no goals
  · exact mem_cons_of_mem _ hm
    -- 🎉 no goals
#align list.duplicate.mem List.Duplicate.mem

theorem Duplicate.mem_cons_self (h : x ∈+ x :: l) : x ∈ l := by
  cases' h with _ h _ _ h
  -- ⊢ x ∈ l
  · exact h
    -- 🎉 no goals
  · exact h.mem
    -- 🎉 no goals
#align list.duplicate.mem_cons_self List.Duplicate.mem_cons_self

@[simp]
theorem duplicate_cons_self_iff : x ∈+ x :: l ↔ x ∈ l :=
  ⟨Duplicate.mem_cons_self, Mem.duplicate_cons_self⟩
#align list.duplicate_cons_self_iff List.duplicate_cons_self_iff

theorem Duplicate.ne_nil (h : x ∈+ l) : l ≠ [] := fun H => (mem_nil_iff x).mp (H ▸ h.mem)
#align list.duplicate.ne_nil List.Duplicate.ne_nil

@[simp]
theorem not_duplicate_nil (x : α) : ¬x ∈+ [] := fun H => H.ne_nil rfl
#align list.not_duplicate_nil List.not_duplicate_nil

theorem Duplicate.ne_singleton (h : x ∈+ l) (y : α) : l ≠ [y] := by
  induction' h with l' h z l' h _
  -- ⊢ x :: l' ≠ [y]
  · simp [ne_nil_of_mem h]
    -- 🎉 no goals
  · simp [ne_nil_of_mem h.mem]
    -- 🎉 no goals
#align list.duplicate.ne_singleton List.Duplicate.ne_singleton

@[simp]
theorem not_duplicate_singleton (x y : α) : ¬x ∈+ [y] := fun H => H.ne_singleton _ rfl
#align list.not_duplicate_singleton List.not_duplicate_singleton

theorem Duplicate.elim_nil (h : x ∈+ []) : False :=
  not_duplicate_nil x h
#align list.duplicate.elim_nil List.Duplicate.elim_nil

theorem Duplicate.elim_singleton {y : α} (h : x ∈+ [y]) : False :=
  not_duplicate_singleton x y h
#align list.duplicate.elim_singleton List.Duplicate.elim_singleton

theorem duplicate_cons_iff {y : α} : x ∈+ y :: l ↔ y = x ∧ x ∈ l ∨ x ∈+ l := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ y = x ∧ x ∈ l ∨ x ∈+ l
  · cases' h with _ hm _ _ hm
    -- ⊢ x = x ∧ x ∈ l ∨ x ∈+ l
    · exact Or.inl ⟨rfl, hm⟩
      -- 🎉 no goals
    · exact Or.inr hm
      -- 🎉 no goals
  · rcases h with (⟨rfl | h⟩ | h)
    -- ⊢ x ∈+ x :: l
    · simpa
      -- 🎉 no goals
    · exact h.cons_duplicate
      -- 🎉 no goals
#align list.duplicate_cons_iff List.duplicate_cons_iff

theorem Duplicate.of_duplicate_cons {y : α} (h : x ∈+ y :: l) (hx : x ≠ y) : x ∈+ l := by
  simpa [duplicate_cons_iff, hx.symm] using h
  -- 🎉 no goals
#align list.duplicate.of_duplicate_cons List.Duplicate.of_duplicate_cons

theorem duplicate_cons_iff_of_ne {y : α} (hne : x ≠ y) : x ∈+ y :: l ↔ x ∈+ l := by
  simp [duplicate_cons_iff, hne.symm]
  -- 🎉 no goals
#align list.duplicate_cons_iff_of_ne List.duplicate_cons_iff_of_ne

theorem Duplicate.mono_sublist {l' : List α} (hx : x ∈+ l) (h : l <+ l') : x ∈+ l' := by
  induction' h with l₁ l₂ y _ IH l₁ l₂ y h IH
  · exact hx
    -- 🎉 no goals
  · exact (IH hx).duplicate_cons _
    -- 🎉 no goals
  · rw [duplicate_cons_iff] at hx ⊢
    -- ⊢ y = x ∧ x ∈ l₂ ∨ x ∈+ l₂
    rcases hx with (⟨rfl, hx⟩ | hx)
    -- ⊢ y = y ∧ y ∈ l₂ ∨ y ∈+ l₂
    · simp [h.subset hx]
      -- 🎉 no goals
    · simp [IH hx]
      -- 🎉 no goals
#align list.duplicate.mono_sublist List.Duplicate.mono_sublist

/-- The contrapositive of `List.nodup_iff_sublist`. -/
theorem duplicate_iff_sublist : x ∈+ l ↔ [x, x] <+ l := by
  induction' l with y l IH
  -- ⊢ x ∈+ [] ↔ [x, x] <+ []
  · simp
    -- 🎉 no goals
  · by_cases hx : x = y
    -- ⊢ x ∈+ y :: l ↔ [x, x] <+ y :: l
    · simp [hx, cons_sublist_cons_iff, singleton_sublist]
      -- 🎉 no goals
    · rw [duplicate_cons_iff_of_ne hx, IH]
      -- ⊢ [x, x] <+ l ↔ [x, x] <+ y :: l
      refine' ⟨sublist_cons_of_sublist y, fun h => _⟩
      -- ⊢ [x, x] <+ l
      cases h
      -- ⊢ [x, x] <+ l
      · assumption
        -- 🎉 no goals
      · contradiction
        -- 🎉 no goals
#align list.duplicate_iff_sublist List.duplicate_iff_sublist

theorem nodup_iff_forall_not_duplicate : Nodup l ↔ ∀ x : α, ¬x ∈+ l := by
  simp_rw [nodup_iff_sublist, duplicate_iff_sublist]
  -- 🎉 no goals
#align list.nodup_iff_forall_not_duplicate List.nodup_iff_forall_not_duplicate

theorem exists_duplicate_iff_not_nodup : (∃ x : α, x ∈+ l) ↔ ¬Nodup l := by
  simp [nodup_iff_forall_not_duplicate]
  -- 🎉 no goals
#align list.exists_duplicate_iff_not_nodup List.exists_duplicate_iff_not_nodup

theorem Duplicate.not_nodup (h : x ∈+ l) : ¬Nodup l := fun H =>
  nodup_iff_forall_not_duplicate.mp H _ h
#align list.duplicate.not_nodup List.Duplicate.not_nodup

theorem duplicate_iff_two_le_count [DecidableEq α] : x ∈+ l ↔ 2 ≤ count x l := by
  simp [duplicate_iff_sublist, le_count_iff_replicate_sublist]
  -- 🎉 no goals
#align list.duplicate_iff_two_le_count List.duplicate_iff_two_le_count

instance decidableDuplicate [DecidableEq α] (x : α) : ∀ l : List α, Decidable (x ∈+ l)
  | [] => isFalse (not_duplicate_nil x)
  | y :: l =>
    match decidableDuplicate x l with
    | isTrue h => isTrue (h.duplicate_cons y)
    | isFalse h =>
      if hx : y = x ∧ x ∈ l then isTrue (hx.left.symm ▸ List.Mem.duplicate_cons_self hx.right)
      else isFalse (by simpa [duplicate_cons_iff, h] using hx)
                       -- 🎉 no goals
#align list.decidable_duplicate List.decidableDuplicate

end List

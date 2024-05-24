/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Nodup

#align_import data.list.dedup from "leanprover-community/mathlib"@"d9e96a3e3e0894e93e10aff5244f4c96655bac1c"

/-!
# Erasure of duplicates in a list

This file proves basic results about `List.dedup` (definition in `Data.List.Defs`).
`dedup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.

## Tags

duplicate, multiplicity, nodup, `nub`
-/


universe u

namespace List

variable {α : Type u} [DecidableEq α]

@[simp]
theorem dedup_nil : dedup [] = ([] : List α) :=
  rfl
#align list.dedup_nil List.dedup_nil

theorem dedup_cons_of_mem' {a : α} {l : List α} (h : a ∈ dedup l) : dedup (a :: l) = dedup l :=
  pwFilter_cons_of_neg <| by simpa only [forall_mem_ne, not_not] using h
#align list.dedup_cons_of_mem' List.dedup_cons_of_mem'

theorem dedup_cons_of_not_mem' {a : α} {l : List α} (h : a ∉ dedup l) :
    dedup (a :: l) = a :: dedup l :=
  pwFilter_cons_of_pos <| by simpa only [forall_mem_ne] using h
#align list.dedup_cons_of_not_mem' List.dedup_cons_of_not_mem'

@[simp]
theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  have := not_congr (@forall_mem_pwFilter α (· ≠ ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, not_not] using this
  · intros x y z xz
    exact not_and_or.1 <| mt (fun h ↦ h.1.trans h.2) xz
#align list.mem_dedup List.mem_dedup

@[simp]
theorem dedup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) : dedup (a :: l) = dedup l :=
  dedup_cons_of_mem' <| mem_dedup.2 h
#align list.dedup_cons_of_mem List.dedup_cons_of_mem

@[simp]
theorem dedup_cons_of_not_mem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a :: dedup l :=
  dedup_cons_of_not_mem' <| mt mem_dedup.1 h
#align list.dedup_cons_of_not_mem List.dedup_cons_of_not_mem

theorem dedup_sublist : ∀ l : List α, dedup l <+ l :=
  pwFilter_sublist
#align list.dedup_sublist List.dedup_sublist

theorem dedup_subset : ∀ l : List α, dedup l ⊆ l :=
  pwFilter_subset
#align list.dedup_subset List.dedup_subset

theorem subset_dedup (l : List α) : l ⊆ dedup l := fun _ => mem_dedup.2
#align list.subset_dedup List.subset_dedup

theorem nodup_dedup : ∀ l : List α, Nodup (dedup l) :=
  pairwise_pwFilter
#align list.nodup_dedup List.nodup_dedup

theorem headI_dedup [Inhabited α] (l : List α) :
    l.dedup.headI = if l.headI ∈ l.tail then l.tail.dedup.headI else l.headI :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
#align list.head_dedup List.headI_dedup

theorem tail_dedup [Inhabited α] (l : List α) :
    l.dedup.tail = if l.headI ∈ l.tail then l.tail.dedup.tail else l.tail.dedup :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
#align list.tail_dedup List.tail_dedup

theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self
#align list.dedup_eq_self List.dedup_eq_self

theorem dedup_eq_cons (l : List α) (a : α) (l' : List α) :
    l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l.dedup.tail = l' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨mem_dedup.1 (h.symm ▸ mem_cons_self _ _), fun ha => ?_, by rw [h, tail_cons]⟩
    have := count_pos_iff_mem.2 ha
    have : count a l.dedup ≤ 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h, count_cons_self] at this
    omega
  · have := @List.cons_head!_tail α ⟨a⟩ _ (ne_nil_of_mem (mem_dedup.2 h.1))
    have hal : a ∈ l.dedup := mem_dedup.2 h.1
    rw [← this, mem_cons, or_iff_not_imp_right] at hal
    exact this ▸ h.2.2.symm ▸ cons_eq_cons.2 ⟨(hal (h.2.2.symm ▸ h.2.1)).symm, rfl⟩
#align list.dedup_eq_cons List.dedup_eq_cons

@[simp]
theorem dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = [] := by
  induction' l with a l hl
  · exact Iff.rfl
  · by_cases h : a ∈ l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h]
    · simp only [List.dedup_cons_of_not_mem h, List.cons_ne_nil]
#align list.dedup_eq_nil List.dedup_eq_nil

protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h
#align list.nodup.dedup List.Nodup.dedup

@[simp]
theorem dedup_idem {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idem
#align list.dedup_idempotent List.dedup_idem

theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ := by
  induction' l₁ with a l₁ IH; · rfl
  simp only [cons_union] at *
  rw [← IH, cons_append]
  by_cases h : a ∈ dedup (l₁ ++ l₂)
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
  · rw [dedup_cons_of_not_mem' h, insert_of_not_mem h]
#align list.dedup_append List.dedup_append

theorem replicate_dedup {x : α} : ∀ {k}, k ≠ 0 → (replicate k x).dedup = [x]
  | 0, h => (h rfl).elim
  | 1, _ => rfl
  | n + 2, _ => by
    rw [replicate_succ, dedup_cons_of_mem (mem_replicate.2 ⟨n.succ_ne_zero, rfl⟩),
      replicate_dedup n.succ_ne_zero]
#align list.replicate_dedup List.replicate_dedup

theorem count_dedup (l : List α) (a : α) : l.dedup.count a = if a ∈ l then 1 else 0 := by
  simp_rw [count_eq_of_nodup <| nodup_dedup l, mem_dedup]
#align list.count_dedup List.count_dedup

end List

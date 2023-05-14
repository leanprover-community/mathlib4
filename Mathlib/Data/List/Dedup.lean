/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

! This file was ported from Lean 3 source module data.list.dedup
! leanprover-community/mathlib commit f694c7dead66f5d4c80f446c796a5aad14707f0e
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathlib.Data.List.Nodup

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
  simpa only [dedup, forall_mem_ne, not_not] using this
  intros x y z xz
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

theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self
#align list.dedup_eq_self List.dedup_eq_self

protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h
#align list.nodup.dedup List.Nodup.dedup

@[simp]
theorem dedup_idempotent {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idempotent
#align list.dedup_idempotent List.dedup_idempotent

theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ := by
  induction' l₁ with a l₁ IH; · rfl
  simp only [instUnionList, cons_union] at *
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

/-- Summing the count of `x` over a list filtered by some `p` is just `countp` applied to `p` -/
theorem sum_map_count_dedup_filter_eq_countp (p : α → Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countp p := by
  induction' l with a as h
  · simp
  · simp_rw [List.countp_cons, List.count_cons', List.sum_map_add]
    congr 1
    · refine' _root_.trans _ h
      by_cases ha : a ∈ as
      · simp [dedup_cons_of_mem ha]
      · simp only [dedup_cons_of_not_mem ha, List.filter]
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · by_cases hp : p a
      · refine' _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h]) _
        simp [hp, count_dedup]
      · refine' _root_.trans (List.sum_eq_zero fun n hn => _) (by simp [hp])
        obtain ⟨a', ha'⟩ := List.mem_map.1 hn
        split_ifs at ha' with ha
        · simp only [ha, mem_filter, mem_dedup, find?, mem_cons, true_or, hp,
            and_false, false_and] at ha'
        · exact ha'.2.symm
#align list.sum_map_count_dedup_filter_eq_countp List.sum_map_count_dedup_filter_eq_countp

theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countp (fun _ => True) l
#align list.sum_map_count_dedup_eq_length List.sum_map_count_dedup_eq_length

end List

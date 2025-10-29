/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Lattice
import Batteries.Data.List.Pairwise

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

variable {α β : Type*} [DecidableEq α]

@[simp]
theorem dedup_nil : dedup [] = ([] : List α) :=
  rfl

theorem dedup_cons_of_mem' {a : α} {l : List α} (h : a ∈ dedup l) : dedup (a :: l) = dedup l :=
  pwFilter_cons_of_neg <| by simpa only [forall_mem_ne, not_not] using h

theorem dedup_cons_of_notMem' {a : α} {l : List α} (h : a ∉ dedup l) :
    dedup (a :: l) = a :: dedup l :=
  pwFilter_cons_of_pos <| by simpa only [forall_mem_ne] using h

theorem dedup_cons' (a : α) (l : List α) :
    dedup (a :: l) = if a ∈ dedup l then dedup l else a :: dedup l := by
  split <;> simp [dedup_cons_of_mem', dedup_cons_of_notMem', *]

@[deprecated (since := "2025-05-23")] alias dedup_cons_of_not_mem' := dedup_cons_of_notMem'

@[simp]
theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  have := not_congr (@forall_mem_pwFilter α (· ≠ ·) _ ?_ a l)
  · simpa only [dedup, forall_mem_ne, not_not] using this
  · intro x y z xz
    exact not_and_or.1 <| mt (fun h ↦ h.1.trans h.2) xz

@[simp]
theorem dedup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) : dedup (a :: l) = dedup l :=
  dedup_cons_of_mem' <| mem_dedup.2 h

@[simp]
theorem dedup_cons_of_notMem {a : α} {l : List α} (h : a ∉ l) : dedup (a :: l) = a :: dedup l :=
  dedup_cons_of_notMem' <| mt mem_dedup.1 h

@[deprecated (since := "2025-05-23")] alias dedup_cons_of_not_mem := dedup_cons_of_notMem

theorem dedup_cons (a : α) (l : List α) :
    dedup (a :: l) = if a ∈ l then dedup l else a :: dedup l := by
  simpa using dedup_cons' a l

theorem dedup_sublist : ∀ l : List α, dedup l <+ l :=
  pwFilter_sublist

theorem dedup_subset : ∀ l : List α, dedup l ⊆ l :=
  pwFilter_subset

theorem subset_dedup (l : List α) : l ⊆ dedup l := fun _ => mem_dedup.2

theorem nodup_dedup : ∀ l : List α, Nodup (dedup l) :=
  pairwise_pwFilter

theorem headI_dedup [Inhabited α] (l : List α) :
    l.dedup.headI = if l.headI ∈ l.tail then l.tail.dedup.headI else l.headI :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]

theorem tail_dedup [Inhabited α] (l : List α) :
    l.dedup.tail = if l.headI ∈ l.tail then l.tail.dedup.tail else l.tail.dedup :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]

theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self

theorem dedup_eq_cons (l : List α) (a : α) (l' : List α) :
    l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l.dedup.tail = l' := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · refine ⟨mem_dedup.1 (h.symm ▸ mem_cons_self), fun ha => ?_, by rw [h, tail_cons]⟩
    have := count_pos_iff.2 ha
    have : count a l.dedup ≤ 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    rw [h, count_cons_self] at this
    cutsat
  · have := @List.cons_head!_tail α ⟨a⟩ _ (ne_nil_of_mem (mem_dedup.2 h.1))
    have hal : a ∈ l.dedup := mem_dedup.2 h.1
    rw [← this, mem_cons, or_iff_not_imp_right] at hal
    exact this ▸ h.2.2.symm ▸ cons_eq_cons.2 ⟨(hal (h.2.2.symm ▸ h.2.1)).symm, rfl⟩

@[simp]
theorem dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = [] := by
  induction l with
  | nil => exact Iff.rfl
  | cons a l hl =>
    by_cases h : a ∈ l
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h, reduceCtorEq]
    · simp only [List.dedup_cons_of_notMem h, List.cons_ne_nil]

protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h

@[simp]
theorem dedup_idem {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idem

theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ := by
  induction l₁ with | nil => rfl | cons a l₁ IH => ?_
  simp only [cons_union] at *
  rw [← IH, cons_append]
  by_cases h : a ∈ dedup (l₁ ++ l₂)
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
  · rw [dedup_cons_of_notMem' h, insert_of_not_mem h]

theorem dedup_map_of_injective [DecidableEq β] {f : α → β} (hf : Function.Injective f)
    (xs : List α) :
    (xs.map f).dedup = xs.dedup.map f := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [map_cons]
    by_cases h : x ∈ xs
    · rw [dedup_cons_of_mem h, dedup_cons_of_mem (mem_map_of_mem h), ih]
    · rw [dedup_cons_of_notMem h, dedup_cons_of_notMem <| (mem_map_of_injective hf).not.mpr h, ih,
        map_cons]

/-- Note that the weaker `List.Subset.dedup_append_left` is proved later. -/
theorem Subset.dedup_append_right {xs ys : List α} (h : xs ⊆ ys) :
    dedup (xs ++ ys) = dedup ys := by
  rw [List.dedup_append, Subset.union_eq_right (List.Subset.trans h <| subset_dedup _)]

theorem Disjoint.union_eq {xs ys : List α} (h : Disjoint xs ys) :
    xs ∪ ys = xs.dedup ++ ys := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [cons_union]
    rw [disjoint_cons_left] at h
    by_cases hx : x ∈ xs
    · rw [dedup_cons_of_mem hx, insert_of_mem (mem_union_left hx _), ih h.2]
    · rw [dedup_cons_of_notMem hx, insert_of_not_mem, ih h.2, cons_append]
      rw [mem_union_iff, not_or]
      exact ⟨hx, h.1⟩

theorem Disjoint.dedup_append {xs ys : List α} (h : Disjoint xs ys) :
    dedup (xs ++ ys) = dedup xs ++ dedup ys := by
  rw [List.dedup_append, Disjoint.union_eq]
  intro a hx hy
  exact h hx (mem_dedup.mp hy)

theorem replicate_dedup {x : α} : ∀ {k}, k ≠ 0 → (replicate k x).dedup = [x]
  | 0, h => (h rfl).elim
  | 1, _ => rfl
  | n + 2, _ => by
    rw [replicate_succ, dedup_cons_of_mem (mem_replicate.2 ⟨n.succ_ne_zero, rfl⟩),
      replicate_dedup n.succ_ne_zero]

theorem count_dedup (l : List α) (a : α) : l.dedup.count a = if a ∈ l then 1 else 0 := by
  simp_rw [count_eq_of_nodup <| nodup_dedup l, mem_dedup]

theorem Perm.dedup {l₁ l₂ : List α} (p : l₁ ~ l₂) : dedup l₁ ~ dedup l₂ :=
  perm_iff_count.2 fun a =>
    if h : a ∈ l₁ then by
      simp [h, nodup_dedup, p.subset h]
    else by
      simp [h, count_eq_zero_of_not_mem, mt p.mem_iff.2]

end List

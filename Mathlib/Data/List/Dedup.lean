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
                             -- 🎉 no goals
#align list.dedup_cons_of_mem' List.dedup_cons_of_mem'

theorem dedup_cons_of_not_mem' {a : α} {l : List α} (h : a ∉ dedup l) :
    dedup (a :: l) = a :: dedup l :=
  pwFilter_cons_of_pos <| by simpa only [forall_mem_ne] using h
                             -- 🎉 no goals
#align list.dedup_cons_of_not_mem' List.dedup_cons_of_not_mem'

@[simp]
theorem mem_dedup {a : α} {l : List α} : a ∈ dedup l ↔ a ∈ l := by
  have := not_congr (@forall_mem_pwFilter α (· ≠ ·) _ ?_ a l)
  -- ⊢ a ∈ dedup l ↔ a ∈ l
  simpa only [dedup, forall_mem_ne, not_not] using this
  -- ⊢ ∀ {x y z : α}, (fun x x_1 => x ≠ x_1) x z → (fun x x_1 => x ≠ x_1) x y ∨ (fu …
  intros x y z xz
  -- ⊢ (fun x x_1 => x ≠ x_1) x y ∨ (fun x x_1 => x ≠ x_1) y z
  exact not_and_or.1 <| mt (fun h ↦ h.1.trans h.2) xz
  -- 🎉 no goals
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
                 -- ⊢ headI (dedup (a :: l)) = if headI (a :: l) ∈ tail (a :: l) then headI (dedup …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align list.head_dedup List.headI_dedup

theorem tail_dedup [Inhabited α] (l : List α) :
    l.dedup.tail = if l.headI ∈ l.tail then l.tail.dedup.tail else l.tail.dedup :=
  match l with
  | [] => rfl
  | a :: l => by by_cases ha : a ∈ l <;> simp [ha, List.dedup_cons_of_mem]
                 -- ⊢ tail (dedup (a :: l)) = if headI (a :: l) ∈ tail (a :: l) then tail (dedup ( …
                                         -- 🎉 no goals
                                         -- 🎉 no goals
#align list.tail_dedup List.tail_dedup

theorem dedup_eq_self {l : List α} : dedup l = l ↔ Nodup l :=
  pwFilter_eq_self
#align list.dedup_eq_self List.dedup_eq_self

theorem dedup_eq_cons (l : List α) (a : α) (l' : List α) :
    l.dedup = a :: l' ↔ a ∈ l ∧ a ∉ l' ∧ l.dedup.tail = l' := by
  refine' ⟨fun h => _, fun h => _⟩
  -- ⊢ a ∈ l ∧ ¬a ∈ l' ∧ tail (dedup l) = l'
  · refine' ⟨mem_dedup.1 (h.symm ▸ mem_cons_self _ _), fun ha => _, by rw [h, tail_cons]⟩
    -- ⊢ False
    have : count a l.dedup ≤ 1 := nodup_iff_count_le_one.1 (nodup_dedup l) a
    -- ⊢ False
    rw [h, count_cons_self, add_le_iff_nonpos_left] at this
    -- ⊢ False
    exact not_le_of_lt (count_pos_iff_mem.2 ha) this
    -- 🎉 no goals
  · have := @List.cons_head!_tail α ⟨a⟩ _ (ne_nil_of_mem (mem_dedup.2 h.1))
    -- ⊢ dedup l = a :: l'
    have hal : a ∈ l.dedup := mem_dedup.2 h.1
    -- ⊢ dedup l = a :: l'
    rw [← this, mem_cons, or_iff_not_imp_right] at hal
    -- ⊢ dedup l = a :: l'
    exact this ▸ h.2.2.symm ▸ cons_eq_cons.2 ⟨(hal (h.2.2.symm ▸ h.2.1)).symm, rfl⟩
    -- 🎉 no goals
#align list.dedup_eq_cons List.dedup_eq_cons

@[simp]
theorem dedup_eq_nil (l : List α) : l.dedup = [] ↔ l = [] := by
  induction' l with a l hl
  -- ⊢ dedup [] = [] ↔ [] = []
  · exact Iff.rfl
    -- 🎉 no goals
  · by_cases h : a ∈ l
    -- ⊢ dedup (a :: l) = [] ↔ a :: l = []
    · simp only [List.dedup_cons_of_mem h, hl, List.ne_nil_of_mem h]
      -- 🎉 no goals
    · simp only [List.dedup_cons_of_not_mem h, List.cons_ne_nil]
      -- 🎉 no goals
#align list.dedup_eq_nil List.dedup_eq_nil

protected theorem Nodup.dedup {l : List α} (h : l.Nodup) : l.dedup = l :=
  List.dedup_eq_self.2 h
#align list.nodup.dedup List.Nodup.dedup

@[simp]
theorem dedup_idempotent {l : List α} : dedup (dedup l) = dedup l :=
  pwFilter_idempotent
#align list.dedup_idempotent List.dedup_idempotent

theorem dedup_append (l₁ l₂ : List α) : dedup (l₁ ++ l₂) = l₁ ∪ dedup l₂ := by
  induction' l₁ with a l₁ IH; · rfl
  -- ⊢ dedup ([] ++ l₂) = [] ∪ dedup l₂
                                -- 🎉 no goals
  simp only [cons_union] at *
  -- ⊢ dedup (a :: l₁ ++ l₂) = List.insert a (l₁ ∪ dedup l₂)
  rw [← IH, cons_append]
  -- ⊢ dedup (a :: (l₁ ++ l₂)) = List.insert a (dedup (l₁ ++ l₂))
  by_cases h : a ∈ dedup (l₁ ++ l₂)
  -- ⊢ dedup (a :: (l₁ ++ l₂)) = List.insert a (dedup (l₁ ++ l₂))
  · rw [dedup_cons_of_mem' h, insert_of_mem h]
    -- 🎉 no goals
  · rw [dedup_cons_of_not_mem' h, insert_of_not_mem h]
    -- 🎉 no goals
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
  -- 🎉 no goals
#align list.count_dedup List.count_dedup

/-- Summing the count of `x` over a list filtered by some `p` is just `countP` applied to `p` -/
theorem sum_map_count_dedup_filter_eq_countP (p : α → Bool) (l : List α) :
    ((l.dedup.filter p).map fun x => l.count x).sum = l.countP p := by
  induction' l with a as h
  -- ⊢ sum (map (fun x => count x []) (filter p (dedup []))) = countP p []
  · simp
    -- 🎉 no goals
  · simp_rw [List.countP_cons, List.count_cons, List.sum_map_add]
    -- ⊢ sum (map (fun i => count i as) (filter p (dedup (a :: as)))) + sum (map (fun …
    congr 1
    -- ⊢ sum (map (fun i => count i as) (filter p (dedup (a :: as)))) = countP p as
    · refine' _root_.trans _ h
      -- ⊢ sum (map (fun i => count i as) (filter p (dedup (a :: as)))) = sum (map (fun …
      by_cases ha : a ∈ as
      -- ⊢ sum (map (fun i => count i as) (filter p (dedup (a :: as)))) = sum (map (fun …
      · simp [dedup_cons_of_mem ha]
        -- 🎉 no goals
      · simp only [dedup_cons_of_not_mem ha, List.filter]
        -- ⊢ sum
        match p a with
        | true => simp only [List.map_cons, List.sum_cons, List.count_eq_zero.2 ha, zero_add]
        | false => simp only
    · by_cases hp : p a
      -- ⊢ sum (map (fun i => if i = a then 1 else 0) (filter p (dedup (a :: as)))) = i …
      · refine' _root_.trans (sum_map_eq_nsmul_single a _ fun _ h _ => by simp [h]) _
        -- ⊢ (count a (filter p (dedup (a :: as))) • if a = a then 1 else 0) = if p a = t …
        simp [hp, count_dedup]
        -- 🎉 no goals
      · refine' _root_.trans (List.sum_eq_zero fun n hn => _) (by simp [hp])
        -- ⊢ n = 0
        obtain ⟨a', ha'⟩ := List.mem_map.1 hn
        -- ⊢ n = 0
        split_ifs at ha' with ha
        -- ⊢ n = 0
        · simp only [ha, mem_filter, mem_dedup, find?, mem_cons, true_or, hp,
            and_false, false_and] at ha'
        · exact ha'.2.symm
          -- 🎉 no goals
#align list.sum_map_count_dedup_filter_eq_countp List.sum_map_count_dedup_filter_eq_countP

theorem sum_map_count_dedup_eq_length (l : List α) :
    (l.dedup.map fun x => l.count x).sum = l.length := by
  simpa using sum_map_count_dedup_filter_eq_countP (fun _ => True) l
  -- 🎉 no goals
#align list.sum_map_count_dedup_eq_length List.sum_map_count_dedup_eq_length

end List

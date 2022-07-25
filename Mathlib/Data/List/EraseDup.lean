/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathlib.Data.List.Pairwise

/-!
# Erasure of duplicates in a List
This file proves basic results about `List.eraseDup` (definition in `Data.Lists.Defs`).
`eraseDup l` returns `l` without its duplicates. It keeps the earliest (that is, rightmost)
occurrence of each.
## Tags
duplicate, multiplicity, nodup, `nub`
-/

namespace List

variable {α : Type u} [DecidableEq α]

@[simp] theorem eraseDup_nil : eraseDup [] = ([] : List α) := rfl

-- theorem eraseDup_cons_of_mem' {a : α} {l : List α} (h : a ∈ eraseDup l) :
--   eraseDup (a :: l) = eraseDup l :=
-- pwFilter_cons_of_neg $ by simp only [forall_mem_ne] using h

-- theorem eraseDup_cons_of_not_mem' {a : α} {l : List α} (h : a ∉ eraseDup l) :
--   eraseDup (a :: l) = a :: eraseDup l :=
-- pw_filter_cons_of_pos $ by simpa only [forall_mem_ne] using h

-- @[simp] theorem mem_eraseDup {a : α} {l : List α} : a ∈ eraseDup l ↔ a ∈ l :=
-- by simpa only [eraseDup, forall_mem_ne, not_not] using not_congr (@forall_mem_pw_filter α (≠) _
--   (λ x y z xz, not_and_distrib.1 $ mt (and.rec eq.trans) xz) a l)

-- @[simp] theorem eraseDup_cons_of_mem {a : α} {l : List α} (h : a ∈ l) :
--   eraseDup (a :: l) = eraseDup l :=
-- eraseDup_cons_of_mem' $ mem_eraseDup.2 h

-- @[simp] theorem eraseDup_cons_of_not_mem {a : α} {l : List α} (h : a ∉ l) :
--   eraseDup (a :: l) = a :: eraseDup l :=
-- eraseDup_cons_of_not_mem' $ mt mem_eraseDup.1 h

-- theorem eraseDup_subList : ∀ (l : List α), eraseDup l <+ l := pw_filter_subList

-- theorem eraseDup_subset : ∀ (l : List α), eraseDup l ⊆ l := pw_filter_subset

-- theorem subset_eraseDup (l : List α) : l ⊆ eraseDup l :=
-- λ a, mem_eraseDup.2

theorem nodup_eraseDup : ∀ l : List α, Nodup (eraseDup l) := pairwise_pwFilter

theorem eraseDup_eq_self {l : List α} : eraseDup l = l ↔ Nodup l := pwFilter_eq_self

protected lemma Nodup.eraseDup {l : List α} (h : l.Nodup) : l.eraseDup = l :=
List.eraseDup_eq_self.2 h

-- @[simp] theorem eraseDup_idempotent {l : List α} : eraseDup (eraseDup l) = eraseDup l :=
-- pw_filter_idempotent

-- theorem eraseDup_append (l₁ l₂ : List α) : eraseDup (l₁ ++ l₂) = l₁ ∪ eraseDup l₂ :=
-- begin
--   induction l₁ with a l₁ IH, {refl}, rw [cons_union, ← IH],
--   show eraseDup (a :: (l₁ ++ l₂)) = insert a (eraseDup (l₁ ++ l₂)),
--   by_cases a ∈ eraseDup (l₁ ++ l₂);
--   [ rw [eraseDup_cons_of_mem' h, insert_of_mem h],
--     rw [eraseDup_cons_of_not_mem' h, insert_of_not_mem h]]
-- end

-- lemma repeat_eraseDup {x : α} : ∀ {k}, k ≠ 0 → (repeat x k).eraseDup = [x]
-- | 0 h := (h rfl).elim
-- | 1 _ := rfl
-- | (n+2) _ := by rw [repeat_succ, eraseDup_cons_of_mem (mem_repeat.2 ⟨n.succ_ne_zero, rfl⟩),
--     repeat_eraseDup n.succ_ne_zero]

end List

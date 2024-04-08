/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.List.Infix

/-!
# Basic properties of `List.eraseIdx`

`List.eraseIdx l k` erases `k`-th element of `l : List α`.
If `k ≥ length l`, then it returns `l`.
-/

namespace List

variable {α β : Type*}

@[simp]
theorem length_eraseIdx {k} {l : List α} (h : k < length l) :
    length (eraseIdx l k) = length l - 1 := calc
  _ = min k (length l) + (length l - (k + 1)) := by simp [eraseIdx_eq_take_drop_succ]
  _ = length l - 1 := by omega

@[simp] theorem eraseIdx_zero (l : List α) : eraseIdx l 0 = tail l := by cases l <;> rfl

theorem eraseIdx_sublist (l : List α) (k : ℕ) : eraseIdx l k <+ l := calc
  eraseIdx l k = take k l ++ drop (k + 1) l := eraseIdx_eq_take_drop_succ ..
  _ <+ take k l ++ drop k l := _
  _ = l := _

theorem eraseIdx_subset (l : List α) (k : ℕ) : eraseIdx l k ⊆ l := (eraseIdx_sublist l k).subset

theorem mem_eraseIdx_iff_get {x : α} :
    ∀ {l} {k}, x ∈ eraseIdx l k ↔ ∃ i : Fin l.length, ↑i ≠ k ∧ l.get i = x
  | [], _ => by simp
  | a::l, 0 => by simp [Fin.exists_fin_succ, mem_iff_get]
  | a::l, k+1 => by
    simp [Fin.exists_fin_succ, mem_eraseIdx_iff_get, @eq_comm _ a, k.succ_ne_zero.symm]

theorem mem_eraseIdx_iff_get? {x : α} {l} {k} : x ∈ eraseIdx l k ↔ ∃ i ≠ k, l.get? i = x := by
  simp_rw [mem_eraseIdx_iff_get, Fin.exists_iff, exists_and_left, get_eq_iff, exists_prop]
  refine exists_congr fun i ↦ Iff.rfl.and <| and_iff_right_of_imp fun h ↦ ?_
  exact (get?_eq_some.1 h).fst

end List

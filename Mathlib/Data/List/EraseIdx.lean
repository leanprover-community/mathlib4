/-
Copyright (c) 2024 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.Data.List.Basic

/-!
# Basic properties of `List.eraseIdx`
-/

namespace List

variable {α β : Type*}

@[simp]
theorem length_eraseIdx : ∀ {k} {l : List α}, k < length l → length (eraseIdx l k) = length l - 1
  | 0, a::l, _ => rfl
  | k + 1, a::b::l, h => by
    rw [length_cons, Nat.succ_lt_succ_iff] at h
    rw [eraseIdx, length_cons, length_eraseIdx h]
    rfl

@[simp] theorem eraseIdx_zero (l : List α) : eraseIdx l 0 = tail l := by cases l <;> rfl

theorem eraseIdx_sublist : ∀ (l : List α) (k : ℕ), eraseIdx l k <+ l
  | [], _ => .refl _
  | a::l, 0 => sublist_cons a l
  | a::l, n + 1 => .cons₂ a <| eraseIdx_sublist l n

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

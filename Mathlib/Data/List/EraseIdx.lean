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

@[simp] theorem eraseIdx_zero (l : List α) : eraseIdx l 0 = tail l := by cases l <;> rfl

theorem eraseIdx_sublist (l : List α) (k : ℕ) : eraseIdx l k <+ l := calc
  eraseIdx l k = take k l ++ drop (k + 1) l := eraseIdx_eq_take_drop_succ ..
  _ <+ take k l ++ drop k l := by gcongr; simp
  _ = l := take_append_drop ..

theorem eraseIdx_subset (l : List α) (k : ℕ) : eraseIdx l k ⊆ l := (eraseIdx_sublist l k).subset

theorem eraseIdx_of_length_le {l : List α} {k : ℕ} (h : length l ≤ k) : eraseIdx l k = l := by
  simp [eraseIdx_eq_take_drop_succ, take_all_of_le h, drop_eq_nil_iff_le, h.trans k.le_succ]

theorem eraseIdx_append_of_lt_length {l : List α} {k : ℕ} (hk : k < length l) (l' : List α) :
    eraseIdx (l ++ l') k = eraseIdx l k ++ l' := by
  rw [eraseIdx_eq_take_drop_succ, take_append_of_le_length, drop_append_of_le_length,
    eraseIdx_eq_take_drop_succ, append_assoc]
  all_goals omega

theorem eraseIdx_append_of_length_le {l : List α} {k : ℕ} (hk : length l ≤ k) (l' : List α) :
    eraseIdx (l ++ l') k = l ++ eraseIdx l' (k - length l) := by
  rw [eraseIdx_eq_take_drop_succ, eraseIdx_eq_take_drop_succ,
    take_append_eq_append_take, drop_append_eq_append_drop,
    take_all_of_le hk, drop_eq_nil_of_le (by omega), nil_append, append_assoc]
  congr
  omega

@[gcongr]
protected theorem IsPrefix.eraseIdx {l l' : List α} (h : l <+: l') (k : ℕ) :
    eraseIdx l k <+: eraseIdx l' k := by
  rcases h with ⟨t, rfl⟩
  rcases lt_or_le k (length l) with hkl|hkl
  case inl => simp [eraseIdx_append_of_lt_length hkl]
  case inr => simp [eraseIdx_append_of_length_le hkl, eraseIdx_of_length_le hkl]

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

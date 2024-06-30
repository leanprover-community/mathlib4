/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# insertNth

Proves various lemmas about `List.insertNth`.
-/

open Function

open Nat hiding one_pos

assert_not_exists Set.range

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

section InsertNth

variable {a : α}

@[simp]
theorem insertNth_zero (s : List α) (x : α) : insertNth 0 x s = x :: s :=
  rfl
#align list.insert_nth_zero List.insertNth_zero

@[simp]
theorem insertNth_succ_nil (n : ℕ) (a : α) : insertNth (n + 1) a [] = [] :=
  rfl
#align list.insert_nth_succ_nil List.insertNth_succ_nil

@[simp]
theorem insertNth_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertNth (n + 1) x (hd :: s) = hd :: insertNth n x s :=
  rfl
#align list.insert_nth_succ_cons List.insertNth_succ_cons

theorem length_insertNth : ∀ n as, n ≤ length as → length (insertNth n a as) = length as + 1
  | 0, _, _ => rfl
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, _ :: as, h => congr_arg Nat.succ <| length_insertNth n as (Nat.le_of_succ_le_succ h)
#align list.length_insert_nth List.length_insertNth

theorem eraseIdx_insertNth (n : ℕ) (l : List α) : (l.insertNth n a).eraseIdx n = l := by
  rw [eraseIdx_eq_modifyNthTail, insertNth, modifyNthTail_modifyNthTail_same]
  exact modifyNthTail_id _ _
#align list.remove_nth_insert_nth List.eraseIdx_insertNth

@[deprecated (since := "2024-05-04")] alias removeNth_insertNth := eraseIdx_insertNth

theorem insertNth_eraseIdx_of_ge :
    ∀ n m as,
      n < length as → n ≤ m → insertNth m a (as.eraseIdx n) = (as.insertNth (m + 1) a).eraseIdx n
  | 0, 0, [], has, _ => (lt_irrefl _ has).elim
  | 0, 0, _ :: as, _, _ => by simp [eraseIdx, insertNth]
  | 0, m + 1, a :: as, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_eraseIdx_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_ge List.insertNth_eraseIdx_of_ge

@[deprecated (since := "2024-05-04")] alias insertNth_removeNth_of_ge := insertNth_eraseIdx_of_ge

theorem insertNth_eraseIdx_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertNth m a (as.eraseIdx n) = (as.insertNth m a).eraseIdx (n + 1)
  | _, 0, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_eraseIdx_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)
#align list.insert_nth_remove_nth_of_le List.insertNth_eraseIdx_of_le

@[deprecated (since := "2024-05-04")] alias insertNth_removeNth_of_le := insertNth_eraseIdx_of_le

theorem insertNth_comm (a b : α) :
    ∀ (i j : ℕ) (l : List α) (_ : i ≤ j) (_ : j ≤ length l),
      (l.insertNth i a).insertNth (j + 1) b = (l.insertNth j b).insertNth i a
  | 0, j, l => by simp [insertNth]
  | i + 1, 0, l => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp only [insertNth_succ_cons, cons.injEq, true_and]
    exact insertNth_comm a b i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)
#align list.insert_nth_comm List.insertNth_comm

theorem mem_insertNth {a b : α} :
    ∀ {n : ℕ} {l : List α} (_ : n ≤ l.length), a ∈ l.insertNth n b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertNth_succ_cons, mem_cons, mem_insertNth (Nat.le_of_succ_le_succ h),
      ← or_assoc, @or_comm (a = a'), or_assoc, mem_cons]
#align list.mem_insert_nth List.mem_insertNth

theorem insertNth_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) :
    insertNth n x l = l := by
  induction' l with hd tl IH generalizing n
  · cases n
    · simp at h
    · simp
  · cases n
    · simp at h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using IH _ h
#align list.insert_nth_of_length_lt List.insertNth_of_length_lt

@[simp]
theorem insertNth_length_self (l : List α) (x : α) : insertNth l.length x l = l ++ [x] := by
  induction' l with hd tl IH
  · simp
  · simpa using IH
#align list.insert_nth_length_self List.insertNth_length_self

theorem length_le_length_insertNth (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertNth n x l).length := by
  rcases le_or_lt n l.length with hn | hn
  · rw [length_insertNth _ _ hn]
    exact (Nat.lt_succ_self _).le
  · rw [insertNth_of_length_lt _ _ _ hn]
#align list.length_le_length_insert_nth List.length_le_length_insertNth

theorem length_insertNth_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertNth n x l).length ≤ l.length + 1 := by
  rcases le_or_lt n l.length with hn | hn
  · rw [length_insertNth _ _ hn]
  · rw [insertNth_of_length_lt _ _ _ hn]
    exact (Nat.lt_succ_self _).le
#align list.length_insert_nth_le_succ List.length_insertNth_le_succ

theorem get_insertNth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)) :
    (insertNth n x l).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  induction' n with n IH generalizing k l
  · simp at hn
  · cases' l with hd tl
    · simp
    · cases k
      · simp [get]
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using IH _ _ hn _

set_option linter.deprecated false in
@[deprecated get_insertNth_of_lt (since := "2023-01-05")]
theorem nthLe_insertNth_of_lt : ∀ (l : List α) (x : α) (n k : ℕ), k < n → ∀ (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)),
    (insertNth n x l).nthLe k hk' = l.nthLe k hk := @get_insertNth_of_lt _
#align list.nth_le_insert_nth_of_lt List.nthLe_insertNth_of_lt

@[simp]
theorem get_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l).get ⟨n, hn'⟩ = x := by
  induction' l with hd tl IH generalizing n
  · simp only [length] at hn
    cases hn
    simp only [insertNth_zero, get_singleton]
  · cases n
    · simp
    · simp only [Nat.succ_le_succ_iff, length] at hn
      simpa using IH _ hn

set_option linter.deprecated false in
@[simp, deprecated get_insertNth_self (since := "2023-01-05")]
theorem nthLe_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l).nthLe n hn' = x := get_insertNth_self _ _ _ hn
#align list.nth_le_insert_nth_self List.nthLe_insertNth_self

theorem get_insertNth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      rwa [length_insertNth _ _ (by omega), Nat.succ_lt_succ_iff])):
    (insertNth n x l).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  induction' l with hd tl IH generalizing n k
  · simp at hk'
  · cases n
    · simp
    · simpa [Nat.add_right_comm] using IH _ _ _

set_option linter.deprecated false in
@[deprecated get_insertNth_add_succ (since := "2023-01-05")]
theorem nthLe_insertNth_add_succ : ∀ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      rwa [length_insertNth _ _ (by omega), Nat.succ_lt_succ_iff])),
    (insertNth n x l).nthLe (n + k + 1) hk = nthLe l (n + k) hk' :=
  @get_insertNth_add_succ _
#align list.nth_le_insert_nth_add_succ List.nthLe_insertNth_add_succ

set_option linter.unnecessarySimpa false in
theorem insertNth_injective (n : ℕ) (x : α) : Function.Injective (insertNth n x) := by
  induction' n with n IH
  · have : insertNth 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h
#align list.insert_nth_injective List.insertNth_injective

end InsertNth

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

assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u

variable {α : Type u}

section InsertNth

variable {a : α}

@[simp]
theorem insertNth_zero (s : List α) (x : α) : insertNth 0 x s = x :: s :=
  rfl

@[simp]
theorem insertNth_succ_nil (n : ℕ) (a : α) : insertNth (n + 1) a [] = [] :=
  rfl

@[simp]
theorem insertNth_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertNth (n + 1) x (hd :: s) = hd :: insertNth n x s :=
  rfl

theorem length_insertNth : ∀ n as, n ≤ length as → length (insertNth n a as) = length as + 1
  | 0, _, _ => rfl
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, _ :: as, h => congr_arg Nat.succ <| length_insertNth n as (Nat.le_of_succ_le_succ h)

theorem eraseIdx_insertNth (n : ℕ) (l : List α) : (l.insertNth n a).eraseIdx n = l := by
  rw [eraseIdx_eq_modifyNthTail, insertNth, modifyNthTail_modifyNthTail_same]
  exact modifyNthTail_id _ _

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

@[deprecated (since := "2024-05-04")] alias insertNth_removeNth_of_ge := insertNth_eraseIdx_of_ge

theorem insertNth_eraseIdx_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertNth m a (as.eraseIdx n) = (as.insertNth m a).eraseIdx (n + 1)
  | _, 0, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertNth_eraseIdx_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

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

#adaptation_note
/--
After nightly-2024-09-06 we can remove the `_root_` prefixes below.
-/
theorem mem_insertNth {a b : α} :
    ∀ {n : ℕ} {l : List α} (_ : n ≤ l.length), a ∈ l.insertNth n b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
  | n + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertNth_succ_cons, mem_cons, mem_insertNth (Nat.le_of_succ_le_succ h),
      ← _root_.or_assoc, @or_comm (a = a'), _root_.or_assoc, mem_cons]

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

@[simp]
theorem insertNth_length_self (l : List α) (x : α) : insertNth l.length x l = l ++ [x] := by
  induction' l with hd tl IH
  · simp
  · simpa using IH

theorem length_le_length_insertNth (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertNth n x l).length := by
  rcases le_or_lt n l.length with hn | hn
  · rw [length_insertNth _ _ hn]
    exact (Nat.lt_succ_self _).le
  · rw [insertNth_of_length_lt _ _ _ hn]

theorem length_insertNth_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertNth n x l).length ≤ l.length + 1 := by
  rcases le_or_lt n l.length with hn | hn
  · rw [length_insertNth _ _ hn]
  · rw [insertNth_of_length_lt _ _ _ hn]
    exact (Nat.lt_succ_self _).le

theorem getElem_insertNth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)) :
    (insertNth n x l)[k] = l[k] := by
  induction' n with n IH generalizing k l
  · simp at hn
  · cases' l with hd tl
    · simp
    · cases k
      · simp [get]
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using IH _ _ hn _

theorem get_insertNth_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertNth n x l).length := hk.trans_le (length_le_length_insertNth _ _ _)) :
    (insertNth n x l).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  simp_all [getElem_insertNth_of_lt]

@[simp]
theorem getElem_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l)[n] = x := by
  induction' l with hd tl IH generalizing n
  · simp only [length] at hn
    cases hn
    simp only [insertNth_zero, getElem_singleton]
  · cases n
    · simp
    · simp only [Nat.succ_le_succ_iff, length] at hn
      simpa using IH _ hn

theorem get_insertNth_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertNth n x l).length := (by rwa [length_insertNth _ _ hn, Nat.lt_succ_iff])) :
    (insertNth n x l).get ⟨n, hn'⟩ = x := by
  simp [hn, hn']

theorem getElem_insertNth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      rwa [length_insertNth _ _ (by omega), Nat.succ_lt_succ_iff])) :
    (insertNth n x l)[n + k + 1] = l[n + k] := by
  induction' l with hd tl IH generalizing n k
  · simp at hk'
  · cases n
    · simp
    · simpa [Nat.add_right_comm] using IH _ _ _

theorem get_insertNth_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertNth n x l).length := (by
      rwa [length_insertNth _ _ (by omega), Nat.succ_lt_succ_iff])) :
    (insertNth n x l).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  simp [getElem_insertNth_add_succ, hk, hk']

set_option linter.unnecessarySimpa false in
theorem insertNth_injective (n : ℕ) (x : α) : Function.Injective (insertNth n x) := by
  induction' n with n IH
  · have : insertNth 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h

end InsertNth

end List

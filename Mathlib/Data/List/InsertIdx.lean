/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Basic

/-!
# insertIdx

Proves various lemmas about `List.insertIdx`.
-/

assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u

variable {α : Type u}

section InsertIdx

variable {a : α}

@[simp]
theorem insertIdx_zero (s : List α) (x : α) : insertIdx 0 x s = x :: s :=
  rfl

@[simp]
theorem insertIdx_succ_nil (n : ℕ) (a : α) : insertIdx (n + 1) a [] = [] :=
  rfl

@[simp]
theorem insertIdx_succ_cons (s : List α) (hd x : α) (n : ℕ) :
    insertIdx (n + 1) x (hd :: s) = hd :: insertIdx n x s :=
  rfl

theorem length_insertIdx : ∀ n as, n ≤ length as → length (insertIdx n a as) = length as + 1
  | 0, _, _ => rfl
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, _ :: as, h => congr_arg Nat.succ <| length_insertIdx n as (Nat.le_of_succ_le_succ h)

theorem eraseIdx_insertIdx (n : ℕ) (l : List α) : (l.insertIdx n a).eraseIdx n = l := by
  rw [eraseIdx_eq_modifyTailIdx, insertIdx, modifyTailIdx_modifyTailIdx_same]
  exact modifyTailIdx_id _ _

theorem insertIdx_eraseIdx_of_ge :
    ∀ n m as,
      n < length as → n ≤ m → insertIdx m a (as.eraseIdx n) = (as.insertIdx (m + 1) a).eraseIdx n
  | 0, 0, [], has, _ => (lt_irrefl _ has).elim
  | 0, 0, _ :: as, _, _ => by simp [eraseIdx, insertIdx]
  | 0, _ + 1, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertIdx_eraseIdx_of_ge n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

theorem insertIdx_eraseIdx_of_le :
    ∀ n m as,
      n < length as → m ≤ n → insertIdx m a (as.eraseIdx n) = (as.insertIdx m a).eraseIdx (n + 1)
  | _, 0, _ :: _, _, _ => rfl
  | n + 1, m + 1, a :: as, has, hmn =>
    congr_arg (cons a) <|
      insertIdx_eraseIdx_of_le n m as (Nat.lt_of_succ_lt_succ has) (Nat.le_of_succ_le_succ hmn)

theorem insertIdx_comm (a b : α) :
    ∀ (i j : ℕ) (l : List α) (_ : i ≤ j) (_ : j ≤ length l),
      (l.insertIdx i a).insertIdx (j + 1) b = (l.insertIdx j b).insertIdx i a
  | 0, j, l => by simp [insertIdx]
  | _ + 1, 0, _ => fun h => (Nat.not_lt_zero _ h).elim
  | i + 1, j + 1, [] => by simp
  | i + 1, j + 1, c :: l => fun h₀ h₁ => by
    simp only [insertIdx_succ_cons, cons.injEq, true_and]
    exact insertIdx_comm a b i j l (Nat.le_of_succ_le_succ h₀) (Nat.le_of_succ_le_succ h₁)

theorem mem_insertIdx {a b : α} :
    ∀ {n : ℕ} {l : List α} (_ : n ≤ l.length), a ∈ l.insertIdx n b ↔ a = b ∨ a ∈ l
  | 0, as, _ => by simp
  | _ + 1, [], h => (Nat.not_succ_le_zero _ h).elim
  | n + 1, a' :: as, h => by
    rw [List.insertIdx_succ_cons, mem_cons, mem_insertIdx (Nat.le_of_succ_le_succ h),
      ← or_assoc, @or_comm (a = a'), or_assoc, mem_cons]

theorem insertIdx_of_length_lt (l : List α) (x : α) (n : ℕ) (h : l.length < n) :
    insertIdx n x l = l := by
  induction' l with hd tl IH generalizing n
  · cases n
    · simp at h
    · simp
  · cases n
    · simp at h
    · simp only [Nat.succ_lt_succ_iff, length] at h
      simpa using IH _ h

@[simp]
theorem insertIdx_length_self (l : List α) (x : α) : insertIdx l.length x l = l ++ [x] := by
  induction' l with hd tl IH
  · simp
  · simpa using IH

theorem length_le_length_insertIdx (l : List α) (x : α) (n : ℕ) :
    l.length ≤ (insertIdx n x l).length := by
  rcases le_or_lt n l.length with hn | hn
  · rw [length_insertIdx _ _ hn]
    exact (Nat.lt_succ_self _).le
  · rw [insertIdx_of_length_lt _ _ _ hn]

theorem length_insertIdx_le_succ (l : List α) (x : α) (n : ℕ) :
    (insertIdx n x l).length ≤ l.length + 1 := by
  rcases le_or_lt n l.length with hn | hn
  · rw [length_insertIdx _ _ hn]
  · rw [insertIdx_of_length_lt _ _ _ hn]
    exact (Nat.lt_succ_self _).le

theorem getElem_insertIdx_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertIdx n x l).length := hk.trans_le (length_le_length_insertIdx _ _ _)) :
    (insertIdx n x l)[k] = l[k] := by
  induction' n with n IH generalizing k l
  · simp at hn
  · cases' l with hd tl
    · simp
    · cases k
      · simp [get]
      · rw [Nat.succ_lt_succ_iff] at hn
        simpa using IH _ _ hn _

theorem get_insertIdx_of_lt (l : List α) (x : α) (n k : ℕ) (hn : k < n) (hk : k < l.length)
    (hk' : k < (insertIdx n x l).length := hk.trans_le (length_le_length_insertIdx _ _ _)) :
    (insertIdx n x l).get ⟨k, hk'⟩ = l.get ⟨k, hk⟩ := by
  simp_all [getElem_insertIdx_of_lt]

@[simp]
theorem getElem_insertIdx_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertIdx n x l).length := (by rwa [length_insertIdx _ _ hn, Nat.lt_succ_iff])) :
    (insertIdx n x l)[n] = x := by
  induction' l with hd tl IH generalizing n
  · simp only [length] at hn
    cases hn
    simp only [insertIdx_zero, getElem_singleton]
  · cases n
    · simp
    · simp only [Nat.succ_le_succ_iff, length] at hn
      simpa using IH _ hn

theorem get_insertIdx_self (l : List α) (x : α) (n : ℕ) (hn : n ≤ l.length)
    (hn' : n < (insertIdx n x l).length := (by rwa [length_insertIdx _ _ hn, Nat.lt_succ_iff])) :
    (insertIdx n x l).get ⟨n, hn'⟩ = x := by
  simp [hn, hn']

theorem getElem_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertIdx n x l).length := (by
      rwa [length_insertIdx _ _ (by omega), Nat.succ_lt_succ_iff])) :
    (insertIdx n x l)[n + k + 1] = l[n + k] := by
  induction' l with hd tl IH generalizing n k
  · simp at hk'
  · cases n
    · simp
    · simpa [Nat.add_right_comm] using IH _ _ _

theorem get_insertIdx_add_succ (l : List α) (x : α) (n k : ℕ) (hk' : n + k < l.length)
    (hk : n + k + 1 < (insertIdx n x l).length := (by
      rwa [length_insertIdx _ _ (by omega), Nat.succ_lt_succ_iff])) :
    (insertIdx n x l).get ⟨n + k + 1, hk⟩ = get l ⟨n + k, hk'⟩ := by
  simp [getElem_insertIdx_add_succ, hk, hk']

set_option linter.unnecessarySimpa false in
theorem insertIdx_injective (n : ℕ) (x : α) : Function.Injective (insertIdx n x) := by
  induction' n with n IH
  · have : insertIdx 0 x = cons x := funext fun _ => rfl
    simp [this]
  · rintro (_ | ⟨a, as⟩) (_ | ⟨b, bs⟩) h <;> simpa [IH.eq_iff] using h

@[deprecated (since := "2024-10-21")] alias insertNth_zero := insertIdx_zero
@[deprecated (since := "2024-10-21")] alias insertNth_succ_nil := insertIdx_succ_nil
@[deprecated (since := "2024-10-21")] alias insertNth_succ_cons := insertIdx_succ_cons
@[deprecated (since := "2024-10-21")] alias length_insertNth := length_insertIdx
@[deprecated (since := "2024-10-21")] alias removeNth_insertIdx := eraseIdx_insertIdx
@[deprecated (since := "2024-05-04")] alias removeNth_insertNth := eraseIdx_insertIdx
@[deprecated (since := "2024-10-21")] alias insertNth_eraseIdx_of_ge := insertIdx_eraseIdx_of_ge
@[deprecated (since := "2024-05-04")] alias insertNth_removeNth_of_ge := insertIdx_eraseIdx_of_ge
@[deprecated (since := "2024-10-21")] alias insertNth_eraseIdx_of_le := insertIdx_eraseIdx_of_le
@[deprecated (since := "2024-05-04")] alias insertIdx_removeNth_of_le := insertIdx_eraseIdx_of_le
@[deprecated (since := "2024-10-21")] alias insertNth_comm := insertIdx_comm
@[deprecated (since := "2024-10-21")] alias mem_insertNth := mem_insertIdx
@[deprecated (since := "2024-10-21")] alias insertNth_of_length_lt := insertIdx_of_length_lt
@[deprecated (since := "2024-10-21")] alias insertNth_length_self := insertIdx_length_self
@[deprecated (since := "2024-10-21")] alias length_le_length_insertNth := length_le_length_insertIdx
@[deprecated (since := "2024-10-21")] alias length_insertNth_le_succ := length_insertIdx_le_succ
@[deprecated (since := "2024-10-21")] alias getElem_insertNth_of_lt := getElem_insertIdx_of_lt
@[deprecated (since := "2024-10-21")] alias get_insertNth_of_lt := get_insertIdx_of_lt
@[deprecated (since := "2024-10-21")] alias getElem_insertNth_self := getElem_insertIdx_self
@[deprecated (since := "2024-10-21")] alias get_insertNth_self := get_insertIdx_self
@[deprecated (since := "2024-10-21")] alias getElem_insertNth_add_succ := getElem_insertIdx_add_succ
@[deprecated (since := "2024-10-21")] alias get_insertNth_add_succ := get_insertIdx_add_succ
@[deprecated (since := "2024-10-21")] alias insertNth_injective := insertIdx_injective

end InsertIdx

end List

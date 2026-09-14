/-
Copyright (c) 2026 Whning0513. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Whning0513
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lemmas about `List.toChunks`
-/

@[expose] public section

namespace List

variable {α : Type*}

private theorem flatten_toChunks_go (n : ℕ) (xs : List α) (a : Array α)
    (A : Array (List α)) : (toChunks.go n xs a A).flatten = A.toList.flatten ++ a.toList ++ xs := by
  induction xs generalizing a A with
  | nil => simp [toChunks.go]
  | cons x xs ih =>
    rw [toChunks.go.eq_2]
    split <;> rw [ih] <;> simp [append_assoc]

private theorem length_le_of_mem_toChunks_go {n : ℕ} (hn : 0 < n) (xs : List α)
    (a : Array α) (A : Array (List α)) (ha : a.size ≤ n)
    (hA : ∀ l ∈ A.toList, l.length ≤ n) : ∀ l ∈ toChunks.go n xs a A, l.length ≤ n := by
  induction xs generalizing a A with
  | nil =>
    simp only [toChunks.go.eq_1, Array.toList_push, mem_append, mem_singleton]
    rintro l (hl | rfl)
    · exact hA l hl
    · simpa using ha
  | cons x xs ih =>
    rw [toChunks.go.eq_2]
    split_ifs with hsize
    · apply ih
      · exact Nat.one_le_of_lt hn
      · intro l hl
        rw [Array.toList_push] at hl
        rcases mem_append.mp hl with hl | hl
        · exact hA l hl
        · have : l = a.toList := by simpa using hl
          subst l
          have : a.size = n := by simpa using hsize
          simpa using Nat.le_of_eq this
    · apply ih
      · have : a.size ≠ n := by simpa using hsize
        simp only [Array.size_push]
        omega
      · exact hA

private theorem nil_notMem_toChunks_go (n : ℕ) (xs : List α) (a : Array α)
    (A : Array (List α)) (ha : a.toList ≠ []) (hA : [] ∉ A.toList) :
    [] ∉ toChunks.go n xs a A := by
  induction xs generalizing a A with
  | nil => simp [toChunks.go, ha, hA]
  | cons x xs ih =>
    rw [toChunks.go.eq_2]
    split
    · apply ih
      · simp
      · simpa [Array.toList_push, ha] using hA
    · apply ih
      · simp
      · exact hA

@[simp]
theorem flatten_toChunks (n : ℕ) (xs : List α) : (xs.toChunks n).flatten = xs := by
  rcases n with _ | n
  · cases xs <;> simp [toChunks]
  · cases xs with
    | nil => rw [toChunks.eq_1]; rfl
    | cons x xs =>
      rw [toChunks.eq_3 _ _ _ (Nat.succ_ne_zero _), flatten_toChunks_go]
      simp

@[simp]
theorem toChunks_eq_nil (n : ℕ) (xs : List α) : xs.toChunks n = [] ↔ xs = [] := by
  constructor
  · intro h
    rw [← flatten_toChunks n xs, h]
    rfl
  · rintro rfl
    exact toChunks.eq_1 n

theorem nil_notMem_toChunks (n : ℕ) (xs : List α) : [] ∉ xs.toChunks n := by
  rcases n with _ | n
  · cases xs with
    | nil => simp [toChunks]
    | cons x xs => simp [toChunks]
  · cases xs with
    | nil => rw [toChunks.eq_1]; simp
    | cons x xs =>
      rw [toChunks.eq_3 _ _ _ (Nat.succ_ne_zero _)]
      exact nil_notMem_toChunks_go _ _ _ _ (by simp) (by simp)

theorem ne_nil_of_mem_toChunks {n : ℕ} {xs l : List α} (hl : l ∈ xs.toChunks n) : l ≠ [] := by
  rintro rfl
  exact nil_notMem_toChunks n xs hl

theorem sublist_of_mem_toChunks {n : ℕ} {xs l : List α} (hl : l ∈ xs.toChunks n) : l <+ xs := by
  rw [← flatten_toChunks n xs]
  exact (infix_of_mem_flatten hl).sublist

theorem length_le_of_mem_toChunks {n : ℕ} (hn : n ≠ 0) {xs l : List α}
    (hl : l ∈ xs.toChunks n) : l.length ≤ n := by
  obtain ⟨n, rfl⟩ := n.exists_eq_succ_of_ne_zero hn
  cases xs with
  | nil => simp [toChunks] at hl
  | cons x xs =>
    rw [toChunks.eq_3 _ _ _ (Nat.succ_ne_zero _)] at hl
    exact length_le_of_mem_toChunks_go (Nat.zero_lt_succ _) _ _ _ (by simp) (by simp) _ hl

end List

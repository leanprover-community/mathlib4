/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Mathlib.Data.List.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Common

/-!
# `Take` and `Drop` lemmas for lists

This file provides lemmas about `List.take` and `List.drop` and related functions.
-/

assert_not_exists GroupWithZero
assert_not_exists Lattice
assert_not_exists Prod.swap_eq_iff_eq_swap
assert_not_exists Ring
assert_not_exists Set.range

open Function

open Nat hiding one_pos

namespace List

universe u v w

variable {ι : Type*} {α : Type u} {β : Type v} {γ : Type w} {l₁ l₂ : List α}

/-! ### take, drop -/

theorem take_one_drop_eq_of_lt_length {l : List α} {n : ℕ} (h : n < l.length) :
    (l.drop n).take 1 = [l.get ⟨n, h⟩] := by
  rw [drop_eq_getElem_cons h, take, take]
  simp

@[simp] lemma take_eq_self_iff (x : List α) {n : ℕ} : x.take n = x ↔ x.length ≤ n :=
  ⟨fun h ↦ by rw [← h]; simp; omega, take_of_length_le⟩

@[simp] lemma take_self_eq_iff (x : List α) {n : ℕ} : x = x.take n ↔ x.length ≤ n := by
  rw [Eq.comm, take_eq_self_iff]

@[simp] lemma take_eq_left_iff {x y : List α} {n : ℕ} :
    (x ++ y).take n = x.take n ↔ y = [] ∨ n ≤ x.length := by
  simp [take_append, Nat.sub_eq_zero_iff_le, Or.comm]

@[simp] lemma left_eq_take_iff {x y : List α} {n : ℕ} :
    x.take n = (x ++ y).take n ↔ y = [] ∨ n ≤ x.length := by
  rw [Eq.comm]; apply take_eq_left_iff

@[simp] lemma drop_take_append_drop (x : List α) (m n : ℕ) :
    (x.drop m).take n ++ x.drop (m + n) = x.drop m := by rw [← drop_drop, take_append_drop]

/-- Compared to `drop_take_append_drop`, the order of summands is swapped. -/
@[simp] lemma drop_take_append_drop' (x : List α) (m n : ℕ) :
    (x.drop m).take n ++ x.drop (n + m) = x.drop m := by rw [Nat.add_comm, drop_take_append_drop]

/-- `take_concat_get` in simp normal form -/
lemma take_concat_get' (l : List α) (i : ℕ) (h : i < l.length) :
    l.take i ++ [l[i]] = l.take (i + 1) := by simp

theorem cons_getElem_drop_succ {l : List α} {n : Nat} {h : n < l.length} :
    l[n] :: l.drop (n + 1) = l.drop n :=
  (drop_eq_getElem_cons h).symm

theorem cons_get_drop_succ {l : List α} {n} :
    l.get n :: l.drop (n.1 + 1) = l.drop n.1 :=
  (drop_eq_getElem_cons n.2).symm

lemma drop_length_sub_one {l : List α} (h : l ≠ []) : l.drop (l.length - 1) = [l.getLast h] := by
  induction l with
  | nil => aesop
  | cons a l ih =>
    by_cases hl : l = []
    · aesop
    rw [length_cons, Nat.add_one_sub_one, List.drop_length_cons hl a]
    simp [getLast_cons, hl]

section TakeI

variable [Inhabited α]

@[simp]
theorem takeI_length : ∀ n l, length (@takeI α _ n l) = n
  | 0, _ => rfl
  | _ + 1, _ => congr_arg succ (takeI_length _ _)

@[simp]
theorem takeI_nil : ∀ n, takeI n (@nil α) = replicate n default
  | 0 => rfl
  | _ + 1 => congr_arg (cons _) (takeI_nil _)

theorem takeI_eq_take : ∀ {n} {l : List α}, n ≤ length l → takeI n l = take n l
  | 0, _, _ => rfl
  | _ + 1, _ :: _, h => congr_arg (cons _) <| takeI_eq_take <| le_of_succ_le_succ h

@[simp]
theorem takeI_left (l₁ l₂ : List α) : takeI (length l₁) (l₁ ++ l₂) = l₁ :=
  (takeI_eq_take (by simp only [length_append, Nat.le_add_right])).trans take_left

theorem takeI_left' {l₁ l₂ : List α} {n} (h : length l₁ = n) : takeI n (l₁ ++ l₂) = l₁ := by
  rw [← h]; apply takeI_left

end TakeI

/- The following section replicates the theorems above but for `takeD`. -/
section TakeD

@[simp]
theorem takeD_length : ∀ n l a, length (@takeD α n l a) = n
  | 0, _, _ => rfl
  | _ + 1, _, _ => congr_arg succ (takeD_length _ _ _)

-- `takeD_nil` is already in batteries

theorem takeD_eq_take : ∀ {n} {l : List α} a, n ≤ length l → takeD n l a = take n l
  | 0, _, _, _ => rfl
  | _ + 1, _ :: _, a, h => congr_arg (cons _) <| takeD_eq_take a <| le_of_succ_le_succ h

@[simp]
theorem takeD_left (l₁ l₂ : List α) (a : α) : takeD (length l₁) (l₁ ++ l₂) a = l₁ :=
  (takeD_eq_take a (by simp only [length_append, Nat.le_add_right])).trans take_left

theorem takeD_left' {l₁ l₂ : List α} {n} {a} (h : length l₁ = n) : takeD n (l₁ ++ l₂) a = l₁ := by
  rw [← h]; apply takeD_left

end TakeD

/-! ### filter -/

section Filter

variable (p)

variable (p : α → Bool)

private theorem span.loop_eq_take_drop :
    ∀ l₁ l₂ : List α, span.loop p l₁ l₂ = (l₂.reverse ++ takeWhile p l₁, dropWhile p l₁)
  | [], l₂ => by simp [span.loop, takeWhile, dropWhile]
  | (a :: l), l₂ => by
    cases hp : p a <;> simp [hp, span.loop, span.loop_eq_take_drop, takeWhile, dropWhile]

@[simp]
theorem span_eq_takeWhile_dropWhile (l : List α) : span p l = (takeWhile p l, dropWhile p l) := by
  simpa using span.loop_eq_take_drop p l []

@[deprecated (since := "2025-02-07")] alias span_eq_take_drop := span_eq_takeWhile_dropWhile

end Filter

/-! ### Miscellaneous lemmas -/

theorem dropSlice_eq (xs : List α) (n m : ℕ) : dropSlice n m xs = xs.take n ++ xs.drop (n + m) := by
  induction n generalizing xs
  · cases xs <;> simp [dropSlice]
  · cases xs <;> simp [dropSlice, *, Nat.succ_add]

@[simp]
theorem length_dropSlice (i j : ℕ) (xs : List α) :
    (List.dropSlice i j xs).length = xs.length - min j (xs.length - i) := by
  induction xs generalizing i j with
  | nil => simp
  | cons x xs xs_ih =>
    cases i <;> simp only [List.dropSlice]
    · cases j with
      | zero => simp
      | succ n => simp_all; omega
    · simp [xs_ih]; omega

theorem length_dropSlice_lt (i j : ℕ) (hj : 0 < j) (xs : List α) (hi : i < xs.length) :
    (List.dropSlice i j xs).length < xs.length := by
  simp; omega

end List

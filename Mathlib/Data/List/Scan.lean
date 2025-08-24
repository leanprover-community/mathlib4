/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Batteries.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic

/-!
# List scan

Prove basic results about `List.scanl` and `List.scanr`.
-/

open Nat

namespace List

variable {α β : Type*} {f : β → α → β} {b : β} {a : α} {l : List α}

/-! ### List.scanl -/

@[simp]
theorem length_scanl : (scanl f b l).length = l.length + 1 := by
  induction l generalizing b <;> simp_all

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl

@[simp]
theorem scanl_ne_nil : scanl f b l ≠ [] := by
  unfold scanl
  split <;> simp

@[simp]
theorem scanl_iff_nil : scanl f b l = [b] ↔ l = [] := by
  constructor
  · cases l <;> simp
  · simp_all

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, singleton_append]

theorem getElem?_scanl_zero : (scanl f b l)[0]? = some b := by
  cases l <;> simp

@[simp]
theorem getElem_scanl_zero : (scanl f b l)[0] = b := by
  cases l <;> simp

@[simp]
theorem head_scanl : (scanl f b l).head scanl_ne_nil = b := by
  cases l <;> simp

theorem getElem?_succ_scanl {i : ℕ} : (scanl f b l)[i + 1]? =
    (scanl f b l)[i]?.bind fun x => l[i]?.map fun y => f x y := by
  induction l generalizing b i with
  | nil =>
    simp only [scanl, getElem?_nil, Option.map_none, Option.bind_fun_none, getElem?_cons_succ]
  | cons hd tl hl =>
    simp only [scanl_cons, singleton_append]
    cases i
    · simp
    · simp only [hl, getElem?_cons_succ]

@[deprecated (since := "2025-02-21")]
alias get?_succ_scanl := getElem?_succ_scanl

theorem getElem_succ_scanl {i : ℕ} (h : i + 1 < (scanl f b l).length) :
    (scanl f b l)[i + 1] =
      f ((scanl f b l)[i]'(Nat.lt_of_succ_lt h))
        (l[i]'(Nat.lt_of_succ_lt_succ (h.trans_eq length_scanl))) := by
  induction i generalizing b l with
  | zero =>
    cases l
    · simp only [scanl, length, lt_self_iff_false] at h
    · simp
  | succ i hi =>
    cases l
    · simp only [scanl, length] at h
      exact absurd h (by omega)
    · simp_rw [scanl_cons]
      rw [getElem_append_right]
      · simp only [length, Nat.zero_add 1, succ_add_sub_one, hi]; rfl
      · simp only [length_singleton]; omega

/-! ### List.scanr -/

variable {f : α → β → β}

@[simp]
theorem scanr_nil : scanr f b [] = [b] :=
  rfl

@[simp]
theorem scanr_ne_nil : scanr f b l ≠ [] := by
  simp [scanr]

@[simp]
theorem scanr_cons : scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, foldr, cons.injEq, and_true]
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih => simp only [foldr, ih]

@[simp]
theorem scanr_iff_nil : scanr f b l = [b] ↔ l = [] := by
  constructor
  · cases l <;> simp
  · simp_all

@[simp]
theorem length_scanr : (scanr f b l).length = l.length + 1 := by
  induction l <;> simp_all

theorem getElem?_scanr_zero : (scanr f b l)[0]? = foldr f b l := by
  cases l <;> simp

@[simp]
theorem getElem_scanr_zero : (scanr f b l)[0] = foldr f b l := by
  cases l <;> simp

@[simp]
theorem head_scanr : (scanr f b l).head scanr_ne_nil = foldr f b l := by
  cases l <;> simp

theorem tail_scanr (h : 0 < l.length) : (scanr f b l).tail = scanr f b l.tail := by
  induction l <;> simp_all

theorem drop_scanr {i : ℕ} (h : i < l.length + 1) :
    (scanr f b l).drop i = scanr f b (l.drop i) := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [← drop_drop]
      simp [ih (by omega), tail_scanr (l := l.drop i) (by rw [length_drop]; omega)]

theorem getElem_scanr {i : ℕ} (h : i < l.length + 1) :
    (scanr f b l)[i]'(by simp [h]) = foldr f b (l.drop i) := by
  induction l generalizing i with
  | nil => simp [h]
  | cons head tail ih =>
      by_cases h' : i = 0
      · simp [h']
      · rw [length_cons] at h
        obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero h'
        simp [@ih m (by omega)]

theorem getElem?_scanr {i : ℕ} (h : i < l.length + 1) :
    (scanr f b l)[i]? = some (foldr f b (l.drop i)) := by
  rw [List.getElem?_eq_getElem (by simp [h]), getElem_scanr h]

end List

/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Batteries.Data.List.Basic
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Option.Basic

/-! ### List.scanl and List.scanr -/

open Nat

namespace List

variable {α β : Type*} {f : β → α → β} {b : β} {a : α} {l : List α}

theorem length_scanl : ∀ a l, length (scanl f a l) = l.length + 1
  | _, [] => rfl
  | a, x :: l => by
    rw [scanl, length_cons, length_cons, ← succ_eq_add_one, congr_arg succ]
    exact length_scanl _ _

@[simp]
theorem scanl_nil (b : β) : scanl f b nil = [b] :=
  rfl

@[simp]
theorem scanl_cons : scanl f b (a :: l) = [b] ++ scanl f (f b a) l := by
  simp only [scanl, singleton_append]

@[simp]
theorem getElem?_scanl_zero : (scanl f b l)[0]? = some b := by
  cases l
  · simp
  · simp

@[simp]
theorem getElem_scanl_zero {h : 0 < (scanl f b l).length} : (scanl f b l)[0] = b := by
  cases l
  · simp
  · simp

theorem getElem?_succ_scanl {i : ℕ} : (scanl f b l)[i + 1]? =
    (scanl f b l)[i]?.bind fun x => l[i]?.map fun y => f x y := by
  induction l generalizing b i with
  | nil =>
    symm
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
        (l[i]'(Nat.lt_of_succ_lt_succ (h.trans_eq (length_scanl b l)))) := by
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

-- scanr
@[simp]
theorem scanr_nil (f : α → β → β) (b : β) : scanr f b [] = [b] :=
  rfl

@[simp]
theorem scanr_cons (f : α → β → β) (b : β) (a : α) (l : List α) :
    scanr f b (a :: l) = foldr f b (a :: l) :: scanr f b l := by
  simp only [scanr, foldr, cons.injEq, and_true]
  induction l generalizing a with
  | nil => rfl
  | cons hd tl ih => simp only [foldr, ih]

end List

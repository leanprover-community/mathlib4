/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Std.Data.List.Basic
import Std.Data.List.Lemmas
import Mathlib.Init.Data.Nat.Basic
import Mathlib.Init.Data.Nat.Lemmas
import Mathlib.Init.Data.List.Basic
/-!
Lemmas for `List` not (yet) in `Std`
-/


open List Nat

namespace List

/-- Length of the list obtained by `map₂` on a pair of lists is the length of the shorter of the two. -/
@[simp]
theorem length_map₂ (f : α → β → γ) (l₁) : ∀ l₂, length (map₂ f l₁ l₂) =
    min (length l₁) (length l₂) := by
  induction l₁ <;> intro l₂ <;> cases l₂ <;>
    simp [*, add_one, min_succ_succ, Nat.zero_min, Nat.min_zero]
#align list.length_map₂ List.length_map₂

/-- Length of the list consisting of an element repeated `n` times is `n`. -/
@[simp]
theorem length_repeat (a : α) (n : ℕ) : length («repeat»  a n) = n := by
  induction n <;> simp [*]
#align list.length_repeat List.length_repeat

/-- Length of the list on removing the `i`th element
when `i` is less than the length of the original list. -/
theorem length_remove_nth : ∀ (l : List α) (i : ℕ),
    i < length l → length (removeNth l i) = length l - 1
  | [], _, _ => rfl
  | _ :: xs, 0, _ => by
     simp [removeNth]
  | x :: xs, i + 1, h => by
    have : i < length xs := lt_of_succ_lt_succ h
    dsimp [removeNth]
    rw [length_remove_nth xs i]
    show length xs - 1 + 1 = length xs + 1 - 1
    rw [Nat.add_sub_cancel (length xs) 1]
    have bd : 1 ≤  length xs := by
      have bd' : i + 1 ≤ length xs := by assumption
      have bd'' : 1 ≤ i + 1 := by
        apply Nat.succ_le_succ
        apply Nat.zero_le
      exact Nat.le_trans bd'' bd'
    exact Nat.sub_add_cancel bd
    assumption

#align list.length_remove_nth List.length_remove_nth

section MapAccumr

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over a list returning the intermediate results and a
a final result.
-/
def mapAccumr (f : α → σ → σ × β) : List α → σ → σ × List β
  | [], c => (c, [])
  | y :: yr, c =>
    let r := mapAccumr f yr c
    let z := f y r.1
    (z.1, z.2 :: r.2)
#align list.map_accumr List.mapAccumr

/-- Length of the list obtained by `mapAccumr`. -/
@[simp]
theorem length_map_accumr : ∀ (f : α → σ → σ × β) (x : List α) (s : σ),
    length (mapAccumr f x s).2 = length x
  | f, _ :: x, s => congrArg succ (length_map_accumr f x s)
  | _, [], _ => rfl
#align list.length_map_accumr List.length_map_accumr

end MapAccumr

section MapAccumr₂

variable {φ : Type w₁} {σ : Type w₂}

/-- Runs a function over two lists returning the intermediate results and a
 a final result.
-/
def mapAccumr₂ (f : α → β → σ → σ × φ) : List α → List β → σ → σ × List φ
  | [], _, c => (c, [])
  | _, [], c => (c, [])
  | x :: xr, y :: yr, c =>
    let r := mapAccumr₂ f xr yr c
    let q := f x y r.1
    (q.1, q.2 :: r.2)
#align list.map_accumr₂ List.mapAccumr₂

/-- Length of a list obtained using `mapAccumr₂`. -/
@[simp]
theorem length_map_accumr₂ :
    ∀ (f : α → β → σ → σ × φ) (x y c), length (mapAccumr₂ f x y c).2 = min (length x) (length y)
  | f, _ :: x, _ :: y, c =>
    calc
      succ (length (mapAccumr₂ f x y c).2) = succ (min (length x) (length y)) :=
        congrArg succ (length_map_accumr₂ f x y c)
      _ = min (succ (length x)) (succ (length y)) := Eq.symm (min_succ_succ (length x) (length y))

  | _, _ :: _, [], _ => rfl
  | _, [], _ :: _, _ => rfl
  | _, [], [], _ => rfl
#align list.length_map_accumr₂ List.length_map_accumr₂

end MapAccumr₂

end List

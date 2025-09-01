/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import Batteries.Data.List.Basic
import Batteries.Tactic.Alias
import Mathlib.Tactic.TypeStar

/-! ### List.modifyLast -/

variable {α : Type*}

namespace List

private theorem modifyLast.go_concat (f : α → α) (a : α) (tl : List α) (r : Array α) :
    modifyLast.go f (tl ++ [a]) r = (r.toListAppend <| modifyLast.go f (tl ++ [a]) #[]) := by
  cases tl with
  | nil =>
    simp only [nil_append, modifyLast.go]; rfl
  | cons hd tl =>
    simp only [cons_append]
    rw [modifyLast.go, modifyLast.go]
    case x_3 | x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat _ _ tl _, modifyLast.go_concat _ _ tl (Array.push #[] hd)]
    simp only [Array.toListAppend_eq, Array.toList_push, nil_append,
      append_assoc]

theorem modifyLast_concat (f : α → α) (a : α) (l : List α) :
    modifyLast f (l ++ [a]) = l ++ [f a] := by
  cases l with
  | nil =>
    simp only [nil_append, modifyLast, modifyLast.go, Array.toListAppend_eq]
  | cons _ tl =>
    simp only [cons_append, modifyLast]
    rw [modifyLast.go]
    case x_3 => exact append_ne_nil_of_right_ne_nil tl (cons_ne_nil a [])
    rw [modifyLast.go_concat, Array.toListAppend_eq, Array.toList_push, List.toList_toArray,
      nil_append, cons_append, nil_append, cons_inj_right]
    exact modifyLast_concat _ _ tl

@[deprecated (since := "2025-02-07")]
alias modifyLast_append_one := modifyLast_concat

theorem modifyLast_append_of_right_ne_nil (f : α → α) (l₁ l₂ : List α) (_ : l₂ ≠ []) :
    modifyLast f (l₁ ++ l₂) = l₁ ++ modifyLast f l₂ := by
  cases l₂ with
  | nil => contradiction
  | cons hd tl =>
    cases tl with
    | nil => exact modifyLast_concat _ hd _
    | cons hd' tl' =>
      rw [append_cons, ← nil_append (hd :: hd' :: tl'), append_cons [], nil_append,
        modifyLast_append_of_right_ne_nil _ (l₁ ++ [hd]) (hd' :: tl') _,
        modifyLast_append_of_right_ne_nil _ [hd] (hd' :: tl') _,
        append_assoc]
      all_goals { exact cons_ne_nil _ _ }

@[deprecated (since := "2025-02-07")]
alias modifyLast_append := modifyLast_append_of_right_ne_nil

end List

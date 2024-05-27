/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Data.DList
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Cases

#align_import data.dlist from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-!
# Difference list

This file provides a few results about `DList`, which is defined in `Batteries`.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `push` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/

universe u

#align dlist Batteries.DList

namespace Batteries.DList

open Function

variable {α : Type u}

#align dlist.of_list Batteries.DList.ofList

/-- Convert a lazily-evaluated `List` to a `DList` -/
def lazy_ofList (l : Thunk (List α)) : DList α :=
  ⟨fun xs => l.get ++ xs, fun t => by simp⟩
#align dlist.lazy_of_list Batteries.DList.lazy_ofList

#align dlist.to_list Batteries.DList.toList

#align dlist.empty Batteries.DList.empty

#align dlist.singleton Batteries.DList.singleton

attribute [local simp] Function.comp

#align dlist.cons Batteries.DList.cons

#align dlist.concat Batteries.DList.push

#align dlist.append Batteries.DList.append

attribute [local simp] ofList toList empty singleton cons push append

theorem toList_ofList (l : List α) : DList.toList (DList.ofList l) = l := by
  cases l; rfl; simp only [DList.toList, DList.ofList, List.cons_append, List.append_nil]
#align dlist.to_list_of_list Batteries.DList.toList_ofList

theorem ofList_toList (l : DList α) : DList.ofList (DList.toList l) = l := by
   cases' l with app inv
   simp only [ofList, toList, mk.injEq]
   funext x
   rw [(inv x)]
#align dlist.of_list_to_list Batteries.DList.ofList_toList

theorem toList_empty : toList (@empty α) = [] := by simp
#align dlist.to_list_empty Batteries.DList.toList_empty

theorem toList_singleton (x : α) : toList (singleton x) = [x] := by simp
#align dlist.to_list_singleton Batteries.DList.toList_singleton

theorem toList_append (l₁ l₂ : DList α) : toList (l₁ ++ l₂) = toList l₁ ++ toList l₂ :=
  show toList (DList.append l₁ l₂) = toList l₁ ++ toList l₂ by
    cases' l₁ with _ l₁_invariant; cases' l₂; simp; rw [l₁_invariant]
#align dlist.to_list_append Batteries.DList.toList_append

theorem toList_cons (x : α) (l : DList α) : toList (cons x l) = x :: toList l := by
  cases l; simp
#align dlist.to_list_cons Batteries.DList.toList_cons

theorem toList_push (x : α) (l : DList α) : toList (push l x) = toList l ++ [x] := by
  cases' l with _ l_invariant; simp; rw [l_invariant]
#align dlist.to_list_concat Batteries.DList.toList_push

end Batteries.DList

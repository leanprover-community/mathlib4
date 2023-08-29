/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Std.Data.DList
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Cases

#align_import data.dlist from "leanprover-community/lean"@"855e5b74e3a52a40552e8f067169d747d48743fd"

/-!
# Difference list

This file provides a few results about `DList`, which is defined in `Std`.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `push` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/

universe u

#align dlist Std.DList

namespace Std.DList

open Function

variable {α : Type u}

#align dlist.of_list Std.DList.ofList

/-- Convert a lazily-evaluated `List` to a `DList` -/
def lazy_ofList (l : Thunk (List α)) : DList α :=
  ⟨fun xs => l.get ++ xs, fun t => by simp⟩
                                      -- 🎉 no goals
#align dlist.lazy_of_list Std.DList.lazy_ofList

#align dlist.to_list Std.DList.toList

#align dlist.empty Std.DList.empty

#align dlist.singleton Std.DList.singleton

attribute [local simp] Function.comp

#align dlist.cons Std.DList.cons

#align dlist.concat Std.DList.push

#align dlist.append Std.DList.append

attribute [local simp] ofList toList empty singleton cons push append

theorem toList_ofList (l : List α) : DList.toList (DList.ofList l) = l := by
  cases l; rfl; simp only [DList.toList, DList.ofList, List.cons_append, List.append_nil]
  -- ⊢ toList (ofList []) = []
           -- ⊢ toList (ofList (head✝ :: tail✝)) = head✝ :: tail✝
                -- 🎉 no goals
#align dlist.to_list_of_list Std.DList.toList_ofList

theorem ofList_toList (l : DList α) : DList.ofList (DList.toList l) = l := by
   cases' l with app inv
   -- ⊢ ofList (toList { apply := app, invariant := inv }) = { apply := app, invaria …
   simp only [ofList, toList, mk.injEq]
   -- ⊢ (fun x => app [] ++ x) = app
   funext x
   -- ⊢ app [] ++ x = app x
   rw [(inv x)]
   -- 🎉 no goals
#align dlist.of_list_to_list Std.DList.ofList_toList

theorem toList_empty : toList (@empty α) = [] := by simp
                                                    -- 🎉 no goals
#align dlist.to_list_empty Std.DList.toList_empty

theorem toList_singleton (x : α) : toList (singleton x) = [x] := by simp
                                                                    -- 🎉 no goals
#align dlist.to_list_singleton Std.DList.toList_singleton

theorem toList_append (l₁ l₂ : DList α) : toList (l₁ ++ l₂) = toList l₁ ++ toList l₂ :=
  show toList (DList.append l₁ l₂) = toList l₁ ++ toList l₂ by
    cases' l₁ with _ l₁_invariant; cases' l₂; simp; rw [l₁_invariant]
    -- ⊢ toList (append { apply := apply✝, invariant := l₁_invariant } l₂) = toList { …
                                   -- ⊢ toList (append { apply := apply✝¹, invariant := l₁_invariant } { apply := ap …
                                              -- ⊢ apply✝¹ (apply✝ []) = apply✝¹ [] ++ apply✝ []
                                                    -- 🎉 no goals
#align dlist.to_list_append Std.DList.toList_append

theorem toList_cons (x : α) (l : DList α) : toList (cons x l) = x :: toList l := by
  cases l; simp
  -- ⊢ toList (cons x { apply := apply✝, invariant := invariant✝ }) = x :: toList { …
           -- 🎉 no goals
#align dlist.to_list_cons Std.DList.toList_cons

theorem toList_push (x : α) (l : DList α) : toList (push l x) = toList l ++ [x] := by
  cases' l with _ l_invariant; simp; rw [l_invariant]
  -- ⊢ toList (push { apply := apply✝, invariant := l_invariant } x) = toList { app …
                               -- ⊢ apply✝ [x] = apply✝ [] ++ [x]
                                     -- 🎉 no goals
#align dlist.to_list_concat Std.DList.toList_push

end Std.DList

/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Std.Data.DList
import Mathlib.Mathport.Rename


/-!
# Difference list

This file provides a few results about `DList`, which is defined in `Std`.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/


/-- Concatenates a list of difference lists to form a single difference list. Similar to
`list.join`. -/
def DList.join {α : Type _} : List (Std.DList α) → Std.DList α
  | [] => Std.DList.empty
  | x :: xs => x ++ DList.join xs
#align dlist.join DList.join

/-- Convert a lazily-evaluated `List` to a `DList` -/
-- Ported from Lean 3 core
def DList.lazy_OfList (l : Thunk (List α)) : Std.DList α :=
⟨fun xs => l.get ++ xs, fun t => by simp⟩
#align dlist.lazy_of_list DList.lazy_OfList

@[simp]
theorem DList_singleton {α : Type _} {a : α} : Std.DList.singleton a = DList.lazy_OfList [a] :=
  rfl
#align dlist_singleton DList_singleton

@[simp]
theorem DList_lazy {α : Type _} {l : List α} : DList.lazy_OfList l = Std.DList.ofList l :=
  rfl
#align dlist_lazy DList_lazy

/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.dlist.basic
! leanprover-community/mathlib commit d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Std.Data.DList
import Mathlib.Mathport.Rename
import Mathlib.Tactic.Cases


/-!
# Difference list

This file provides a few results about `DList`, which is defined in `Std`.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `concat` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/

namespace Std

/-- Concatenates a list of difference lists to form a single difference list. Similar to
`List.join`. -/
def DList.join {α : Type _} : List (DList α) → DList α
  | [] => DList.empty
  | x :: xs => x ++ DList.join xs
#align dlist.join Std.DList.join

/-- Convert a lazily-evaluated `List` to a `DList` -/
-- Ported from Lean 3 core
def DList.lazy_ofList (l : Thunk (List α)) : DList α :=
  ⟨fun xs => l.get ++ xs, fun t => by simp⟩
#align dlist.lazy_of_list Std.DList.lazy_ofList

@[simp]
theorem DList_singleton {α : Type _} {a : α} : DList.singleton a = DList.lazy_ofList [a] :=
  rfl
#align dlist_singleton Std.DList_singleton

@[simp]
theorem DList_lazy {α : Type _} {l : List α} : DList.lazy_ofList l = Std.DList.ofList l :=
  rfl
#align dlist_lazy Std.DList_lazy

-- Porting note: port from lean3
theorem DList.toList_ofList (l : List α) : DList.toList (DList.ofList l) = l := by
  cases l; rfl; simp only [DList.toList, DList.ofList, List.cons_append, List.append_nil]
#align dlist.to_list_of_list Std.DList.toList_ofList

-- Porting note: port from lean3
theorem DList.ofList_toList (l : DList α) : DList.ofList (DList.toList l) = l := by
   cases' l with app inv
   simp only [ofList, toList, mk.injEq]
   funext x
   rw [(inv x)]
#align dlist.of_list_to_list Std.DList.ofList_toList

end Std

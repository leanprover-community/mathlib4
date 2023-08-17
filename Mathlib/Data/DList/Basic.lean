/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.DList.Defs
import Mathlib.Tactic.Basic

#align_import data.dlist.basic from "leanprover-community/mathlib"@"d6aae1bcbd04b8de2022b9b83a5b5b10e10c777d"


/-!
# Difference list

This file provides a few results about `DList`, which is defined in `Std`.

A difference list is a function that, given a list, returns the original content of the
difference list prepended to the given list. It is useful to represent elements of a given type
as `a₁ + ... + aₙ` where `+ : α → α → α` is any operation, without actually computing.

This structure supports `O(1)` `append` and `push` operations on lists, making it
useful for append-heavy uses such as logging and pretty printing.
-/

namespace Std

/-- Concatenates a list of difference lists to form a single difference list. Similar to
`List.join`. -/
def DList.join {α : Type*} : List (DList α) → DList α
  | [] => DList.empty
  | x :: xs => x ++ DList.join xs
#align dlist.join Std.DList.join

@[simp]
theorem DList_singleton {α : Type*} {a : α} : DList.singleton a = DList.lazy_ofList [a] :=
  rfl
#align dlist_singleton Std.DList_singleton

@[simp]
theorem DList_lazy {α : Type*} {l : List α} : DList.lazy_ofList l = Std.DList.ofList l :=
  rfl
#align dlist_lazy Std.DList_lazy

end Std

/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
import Mathlib.Data.DList.Basic
import Mathlib.Control.Traversable.Equiv
import Mathlib.Control.Traversable.Instances

#align_import data.dlist.instances from "leanprover-community/mathlib"@"f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c"

/-!
# Traversable instance for DLists

This file provides the equivalence between `List α` and `DList α` and the traversable instance
for `DList`.
-/


open Function Equiv

namespace Std

variable (α : Type*)

/-- The natural equivalence between lists and difference lists, using
`DList.ofList` and `DList.toList`. -/
def DList.listEquivDList : List α ≃ DList α := by
  refine'
      { toFun := DList.ofList
        invFun := DList.toList.. } <;>
    simp [Function.RightInverse, Function.LeftInverse, DList.toList_ofList, DList.ofList_toList]
    -- 🎉 no goals
    -- 🎉 no goals
#align dlist.list_equiv_dlist Std.DList.listEquivDList

instance : Traversable DList :=
  Equiv.traversable DList.listEquivDList

instance : LawfulTraversable DList :=
  Equiv.isLawfulTraversable DList.listEquivDList

instance {α} : Inhabited (DList α) :=
  ⟨DList.empty⟩

end Std

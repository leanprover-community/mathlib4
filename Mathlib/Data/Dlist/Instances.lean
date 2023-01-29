/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon

! This file was ported from Lean 3 source module data.dlist.instances
! leanprover-community/mathlib commit f7fc89d5d5ff1db2d1242c7bb0e9062ce47ef47c
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Control.Traversable.Equiv
import Mathbin.Control.Traversable.Instances

/-!
# Traversable instance for dlists

This file provides the equivalence between `list α` and `dlist α` and the traversable instance
for `dlist`.
-/


open Function Equiv

namespace Dlist

variable (α : Type _)

/-- The natural equivalence between lists and difference lists, using
`dlist.of_list` and `dlist.to_list`. -/
def listEquivDlist : List α ≃ Dlist α := by
  refine'
      { toFun := Dlist.ofList
        invFun := Dlist.toList.. } <;>
    simp [Function.RightInverse, left_inverse, to_list_of_list, of_list_to_list]
#align dlist.list_equiv_dlist Dlist.listEquivDlist

instance : Traversable Dlist :=
  Equiv.traversable listEquivDlist

instance : IsLawfulTraversable Dlist :=
  Equiv.isLawfulTraversable listEquivDlist

instance {α} : Inhabited (Dlist α) :=
  ⟨Dlist.empty⟩

end Dlist


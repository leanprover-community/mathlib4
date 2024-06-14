/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Notation
import Batteries.Data.List.Basic
/-!
Definitions for `List` not (yet) in `Batteries`
-/

set_option autoImplicit true


open Decidable List

universe u v w

namespace List

#align list.nth List.get?

/-- The head of a list, or the default element of the type is the list is `nil`. -/
def headI [Inhabited α] : List α → α
  | []       => default
  | (a :: _) => a
#align list.head List.headI

@[simp] theorem headI_nil [Inhabited α] : ([] : List α).headI = default := rfl
@[simp] theorem headI_cons [Inhabited α] {h : α} {t : List α} : (h :: t).headI = h := rfl

#align list.map₂ List.zipWith

#noalign list.map_with_index_core

#align list.map_with_index List.mapIdx

#align list.find_index List.findIdx

#align list.update_nth List.set

#align list.bor List.or

#align list.band List.and

#align list.last List.getLast

/-- The last element of a list, with the default if list empty -/
def getLastI [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => getLastI l
#align list.ilast List.getLastI

#align list.init List.dropLast

/-- List with a single given element. -/
@[inline, deprecated List.pure (since := "2024-03-24")]
protected def ret {α : Type u} (a : α) : List α := [a]
#align list.ret List.pure

/-- `≤` implies not `>` for lists. -/
theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun _ _ => rfl
#align list.le_eq_not_gt List.le_eq_not_gt

@[deprecated (since := "2024-06-07")] alias toArray_data := Array.data_toArray

end List

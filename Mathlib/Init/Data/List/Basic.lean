/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib.Mathport.Rename
import Mathlib.Init.Data.Nat.Notation
import Std.Data.Nat.Lemmas
import Std.Data.List.Basic
/-!
Definitions for `List` not (yet) in `Std`
-/

set_option autoImplicit true


open Decidable List

universe u v w

namespace List



open Option Nat


/-- nth element of a list `l` given `n < l.length`. -/
@[deprecated get]
def nthLe (l : List α) (n) (h : n < l.length) : α := get l ⟨n, h⟩

set_option linter.deprecated false in
@[deprecated]
theorem nthLe_eq (l : List α) (n) (h : n < l.length) : nthLe l n h = get l ⟨n, h⟩ := rfl

/-- The head of a list, or the default element of the type is the list is `nil`. -/
def headI [Inhabited α] : List α → α
  | []       => default
  | (a :: _) => a

@[simp] theorem headI_nil [Inhabited α] : ([] : List α).headI = default := rfl
@[simp] theorem headI_cons [Inhabited α] {h : α} {t : List α} : (h :: t).headI = h := rfl


#noalign list.map_with_index_core


/-- Find index of element with given property. -/
@[deprecated findIdx]
def findIndex (p : α → Prop) [DecidablePred p] : List α → ℕ := List.findIdx p





/-- The last element of a list, with the default if list empty -/
def getLastI [Inhabited α] : List α → α
  | [] => default
  | [a] => a
  | [_, b] => b
  | _ :: _ :: l => getLastI l


/-- List with a single given element. -/
@[inline] protected def ret {α : Type u} (a : α) : List α := [a]

/-- `≤` implies not `>` for lists. -/
theorem le_eq_not_gt [LT α] : ∀ l₁ l₂ : List α, (l₁ ≤ l₂) = ¬l₂ < l₁ := fun _ _ => rfl

end List

/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Batteries.Tactic.Alias
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.TypeStar

/-!
# Helper definitions and instances for `Ordering`
-/

universe u

deriving instance Repr for Ordering

namespace Ordering

variable {α : Type*}

@[deprecated (since := "2024-09-13")] alias orElse := «then»

/-- `Compares o a b` means that `a` and `b` have the ordering relation `o` between them, assuming
that the relation `a < b` is defined. -/
-- Porting note: we have removed `@[simp]` here in favour of separate simp lemmas,
-- otherwise this definition will unfold to a match.
def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b

@[deprecated (since := "2024-09-13")] alias toRel := Compares

@[simp] lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl

@[simp] lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl

@[simp] lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

end Ordering

/--
Lift a decidable relation to an `Ordering`,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

/--
Construct an `Ordering` from a type with a decidable `LT` instance,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

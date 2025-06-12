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

/-- `Compares o a b` means that `a` and `b` have the ordering relation `o` between them, assuming
that the relation `a < b` is defined. -/
def Compares [LT α] : Ordering → α → α → Prop
  | lt, a, b => a < b
  | eq, a, b => a = b
  | gt, a, b => a > b

@[simp] lemma compares_lt [LT α] (a b : α) : Compares lt a b = (a < b) := rfl

@[simp] lemma compares_eq [LT α] (a b : α) : Compares eq a b = (a = b) := rfl

@[simp] lemma compares_gt [LT α] (a b : α) : Compares gt a b = (a > b) := rfl

/-- `o₁.dthen fun h => o₂(h)` is like `o₁.then o₂` but `o₂` is allowed to depend on
`h : o₁ = .eq`. -/
@[macro_inline] def dthen :
    (o : Ordering) → (o = .eq → Ordering) → Ordering
  | .eq, f => f rfl
  | o, _ => o

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
def cmp {α : Type u} [LT α] [DecidableLT α] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

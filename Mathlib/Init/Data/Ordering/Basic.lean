/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

import Mathlib.Mathport.Rename

/-!
# Note about `Mathlib/Init/`
The files in `Mathlib/Init` are leftovers from the port from Mathlib3.
(They contain content moved from lean3 itself that Mathlib needed but was not moved to lean4.)

We intend to move all the content of these files out into the main `Mathlib` directory structure.
Contributions assisting with this are appreciated.

`#align` statements without corresponding declarations
(i.e. because the declaration is in Batteries or Lean) can be left here.
These will be deleted soon so will not significantly delay deleting otherwise empty `Init` files.

# Helper definitions and instances for `Ordering`
-/

universe u

deriving instance Repr for Ordering

namespace Ordering

/-- Combine two `Ordering`s lexicographically. -/
@[inline]
def orElse : Ordering → Ordering → Ordering
  | lt, _ => lt
  | eq, o => o
  | gt, _ => gt

/-- The relation corresponding to each `Ordering` constructor (e.g. `.lt.toProp a b` is `a < b`). -/
def toRel {α : Type u} [LT α] : Ordering → α → α → Prop
  | .lt => (· < ·)
  | .eq => Eq
  | .gt => (· > ·)

end Ordering

/--
Lift a decidable relation to an `Ordering`,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq
#align cmp_using cmpUsing

/--
Construct an `Ordering` from a type with a decidable `LT` instance,
assuming that incomparable terms are `Ordering.eq`.
-/
def cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  cmpUsing (· < ·) a b

/-
Copyright (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

/-!  # Helper definitions and instances for `Ordering` -/

universe u v

-- Porting note: ideally, done via `deriving Repr` at site of definition of `Ordering`
instance : Repr Ordering :=
  ⟨fun s _ =>
    match s with
    | .lt => "lt"
    | .eq => "eq"
    | .gt => "gt"⟩

namespace Ordering

@[inline]
def orElse : Ordering → Ordering → Ordering
  | lt, _ => lt
  | eq, o => o
  | gt, _ => gt

end Ordering

def CmpUsing {α : Type u} (lt : α → α → Prop) [DecidableRel lt] (a b : α) : Ordering :=
  if lt a b then Ordering.lt else if lt b a then Ordering.gt else Ordering.eq

def Cmp {α : Type u} [LT α] [DecidableRel ((· < ·) : α → α → Prop)] (a b : α) : Ordering :=
  CmpUsing (· < ·) a b

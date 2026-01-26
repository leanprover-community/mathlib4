import Mathlib.Data.Set.Operations

/-! # `Set.range` on `WithBot` and `WithTop` -/

public section

open Set

variable {α β : Type*}

theorem WithBot.range_eq (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ WithBot.some : α → β)) :=
  Option.range_eq f

theorem WithTop.range_eq (f : WithTop α → β) :
    range f = insert (f ⊤) (range (f ∘ WithBot.some : α → β)) :=
  Option.range_eq f

/-
Copyright (c) 2022 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/

import Mathlib.Data.Set.Image
import Mathlib.Order.TypeTags

/-! # `Set.range` on `WithBot` and `WithTop` -/

open Set

variable {α β : Type*}

theorem WithBot.range_eq (f : WithBot α → β) :
    range f = insert (f ⊥) (range (f ∘ WithBot.some : α → β)) :=
  Option.range_eq f

theorem WithTop.range_eq (f : WithTop α → β) :
    range f = insert (f ⊤) (range (f ∘ WithBot.some : α → β)) :=
  Option.range_eq f

/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Data.Fintype.Option
public import Mathlib.Order.TypeTags

/-!
# Fintype instances for `WithTop α` and `WithBot α`
-/
set_option backward.defeqAttrib.useBackward true

@[expose] public section

variable {α : Type*}

@[to_dual]
instance [Fintype α] : Fintype (WithTop α) :=
  inferInstanceAs <| Fintype (Option α)

@[to_dual]
instance [Finite α] : Finite (WithTop α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _

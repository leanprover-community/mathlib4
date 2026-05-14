/-
Copyright (c) 2025 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Order.TypeTags
public import Mathlib.Data.Finset.Option
import Mathlib.Data.Finset.Attr
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Common
import Mathlib.Tactic.Finiteness.Attr
import Mathlib.Tactic.SetLike

/-!
# Fintype instances for `WithTop α` and `WithBot α`
-/

public section

variable {α : Type*}

@[to_dual]
instance [Fintype α] : Fintype (WithTop α) :=
  inferInstanceAs <| Fintype (Option α)

@[to_dual]
instance [Finite α] : Finite (WithTop α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _
